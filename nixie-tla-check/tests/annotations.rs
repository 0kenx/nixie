//! `@type:` annotations (issue #15).
//!
//! Apalache *requires* annotations, so a drop-in has to read them. These
//! tests pin the three halves that landed: attachment (including
//! interleaved comments inside one `VARIABLES` block – Test1226's shape),
//! the Type1 grammar subset, and seeding – where an annotation is
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

// ======== attachment ========

/// Interleaved comments inside one `VARIABLES` block annotate the *next*
/// name each – Test1226's shape, and the attachment bug's reproducer.
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

/// A trailing comment on a declaration's own line, then the next
/// declaration's annotation on the line after: the two comments are adjacent
/// lines, and read as one group they both took the group's first position –
/// both bound to `msgs`, the second as an `Int`. An annotation's position is
/// the line it starts on (`HandshakeWithTypes.tla`'s shape).
#[test]
fn an_annotation_binds_from_the_line_it_starts_on() {
    let src = r#"
---- MODULE Trailing ----
EXTENDS Integers
VARIABLES
    \* @type: Set(Int);
    msgs,     \* the set of all messages
    \* @type: Int;
    iseqno,   \* Initiator's sequence number
    \* @type: Str;
    istate    \* Initiator's state
Init == msgs = {} /\ iseqno = 0 /\ istate = "init"
Next == UNCHANGED <<msgs, iseqno, istate>>
Inv == istate = "init"
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
            ("msgs".to_string(), "Set(Int);".to_string()),
            ("iseqno".to_string(), "Int;".to_string()),
            ("istate".to_string(), "Str;".to_string()),
        ]
    );
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
        bmc.check(0, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(0)
    );
}

// ======== seeding: the annotation settles the shape ========

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

/// The issue's own named defect, **closed**: `f["b"]` against the settled
/// `Str -> Int` annotation is a *function* application – Apalache's settled
/// shape – because a subject already settled as `Fun` never takes the
/// field-access record preference. The annotation is authoritative.
#[test]
fn a_field_access_against_the_annotation_applies_the_function() {
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
    assert_eq!(claim(src, "Inv"), Outcome::NoViolationWithin(0));
    // And a wrong read at the settled shape is a violation, not a refusal.
    let bad = src.replace("f[\"b\"] = 1", "f[\"b\"] = 2");
    assert_eq!(claim(&bad, "Inv"), Outcome::Violation { step: 0 });
}

/// The preference itself is untouched where it belongs: an *unsettled*
/// subject still takes the record shape on a field access, which is how
/// unannotated heterogeneous records type at all.
#[test]
fn an_unannotated_field_access_still_prefers_the_record() {
    let src = r#"
---- MODULE FieldPlain ----
EXTENDS Integers
VARIABLE f
Init == f = [a |-> 1, b |-> 2]
Next == UNCHANGED f
Inv == f["b"] = 2
====
"#;
    assert_eq!(claim(src, "Inv"), Outcome::NoViolationWithin(0));
}

/// A **conflicting** annotation is a type error (exit 120), never a silent
/// override – the issue's "contradictory annotations accepted silently"
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

// ======== the grammar ========

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
    // A record may be written with square brackets, as Apalache's `record`
    // rule reads it (`ewd998/AsyncTerminationDetection.tla`'s alias).
    round(
        "[a: Int, b: Str]",
        Type::Rec {
            fields: [("a".to_string(), Type::Int), ("b".to_string(), Type::Str)]
                .into_iter()
                .collect(),
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
/// operator types (the variants sub-issue) – never silently accepted.
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

// ======== uninterpreted types ========

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

// ======== operator-signature annotations, checked (issue #41) ========

/// An operator signature is **checked** against the operator's body: the
/// parameters are assumed at their annotated types and the body's inferred
/// result must unify with the annotation's. A signature that matches
/// changes nothing; one that disagrees is a type error (exit 120), and one
/// that names nothing, or miscounts the parameters, is reported as the
/// defect it is.
#[test]
fn an_operator_signature_annotation_is_checked_against_the_body() {
    let ok = r#"
---- MODULE SigOK ----
EXTENDS Integers
\* @type: (Int) => Int;
F(x) == x + 1
VARIABLE
    \* @type: Int;
    x
Init == x = 0
Next == UNCHANGED x
Inv == F(x) = 1
====
"#;
    assert_eq!(claim(ok, "Inv"), Outcome::NoViolationWithin(0));

    // The result type disagrees with the body: a type error, never a
    // silent note.
    let wrong = r#"
---- MODULE SigBad ----
EXTENDS Integers
\* @type: (Int) => Str;
F(x) == x + 1
VARIABLE
    \* @type: Int;
    x
Init == x = 0
Next == UNCHANGED x
Inv == F(x) = 1
====
"#;
    let err = types_err(wrong, "Inv");
    assert!(err.contains("does not match its body"), "{err}");

    // A parameter type that the body contradicts, caught the same way.
    let badparam = r#"
---- MODULE SigBadParam ----
EXTENDS Integers
\* @type: (Str) => Int;
F(x) == x + 1
VARIABLE
    \* @type: Int;
    x
Init == x = 0
Next == UNCHANGED x
Inv == F(x) = 1
====
"#;
    let err = types_err(badparam, "Inv");
    assert!(
        err.contains("does not match its body") || err.contains("does not check"),
        "{err}"
    );

    // Polymorphic within one signature: `(a) => a` on the identity.
    let poly = r#"
---- MODULE SigPoly ----
EXTENDS Integers
\* @type: (a) => a;
F(x) == x
VARIABLE
    \* @type: Int;
    x
Init == x = 0
Next == UNCHANGED x
Inv == F(x) = 0
====
"#;
    assert_eq!(claim(poly, "Inv"), Outcome::NoViolationWithin(0));

    // Wrong arity is a defect in the specification, named as such.
    let arity = r#"
---- MODULE SigArity ----
EXTENDS Integers
\* @type: (Int, Int) => Int;
F(x) == x + 1
VARIABLE
    \* @type: Int;
    x
Init == x = 0
Next == UNCHANGED x
Inv == F(x) = 1
====
"#;
    let err = types_err(arity, "Inv");
    assert!(err.contains("parameter(s) but the operator takes"), "{err}");
}

// ======== the grammar the corpus writes (`$name`, `() => T`) ========

/// `() => T` is the signature of a zero-argument operator – how the corpus
/// annotates a constant written as a definition (`\* @type: () => Set(Int);`
/// on `Empty == {}`, Bug1880's shape). It was refused as `RParen where a
/// type was expected`: the parameter list demanded one parameter.
#[test]
fn the_empty_parameter_list_is_a_signature() {
    use nixie_tla::Type;
    use nixie_tla::annotations::{parse_signature1, parse_type1};
    let sig = parse_signature1("() => Set(Int);")
        .expect("parses")
        .expect("a signature");
    assert!(sig.params.is_empty(), "no parameters");
    assert_eq!(sig.result, Type::Set(Box::new(Type::Int)));
    // The value-type reader names it a signature rather than failing.
    let err = match parse_type1("() => Set(Int);") {
        Ok(_) => panic!("a signature is not a value type"),
        Err(e) => e,
    };
    assert!(err.to_string().contains("signature"), "{err}");
    // A bare `()` is not a type (Apalache's parser rejects it too).
    let err = match parse_type1("()") {
        Ok(_) => panic!("`()` is not a type"),
        Err(e) => e,
    };
    assert!(err.to_string().contains("does not parse"), "{err}");

    // Through a specification: the annotation is checked against the body.
    let src = r#"
---- MODULE EmptySig ----
EXTENDS Integers
VARIABLE
    \* @type: Set(Int);
    set
Init ==
    LET \* @type: () => Set(Int);
        Empty == {}
    IN
    set = Empty
Next == UNCHANGED set
Inv == set = {}
====
"#;
    assert_eq!(claim(src, "Inv"), Outcome::NoViolationWithin(0));
    // … and one that disagrees with the body is the type error it is.
    let src = src
        .replace("Empty == {}", "Empty == {1}")
        .replace("() => Set(Int)", "() => Set(Str)");
    let err = types_err(&src, "Inv");
    assert!(err.contains("does not match its body"), "{err}");
}

/// `$name` is a reference to the `@typeAlias` named `name` (Apalache's
/// `aliasReference`): `@typeAlias: set = Set(Int);` with `@type: $set;` on
/// a variable seeds that variable with `Set(Int)`. A reference no alias
/// defines is a type constant of its own, `$name`, apart from `name` the
/// type variable – never a parse error, which is what the corpus's
/// `MegaSpec1`, `Invariants`, `Test1182` and the `MC*` specs all met.
#[test]
fn a_dollar_name_is_an_alias_reference() {
    use nixie_tla::Type;
    use nixie_tla::annotations::{parse_signature1, parse_type1};
    assert_eq!(
        parse_type1("$set;").expect("parses").0,
        Type::Uninterpreted("$set".to_string())
    );
    // In a signature's parameters and result alike.
    let sig = parse_signature1("$transfer => TX;")
        .expect("parses")
        .expect("a signature");
    assert_eq!(
        sig.params,
        vec![Type::Uninterpreted("$transfer".to_string())]
    );
    assert_eq!(sig.result, Type::Uninterpreted("TX".to_string()));

    let src = r#"
---- MODULE Aliased ----
EXTENDS Integers, FiniteSets, Sequences
VARIABLES
    \* @typeAlias: set = Set(Int);
    \* @typeAlias: state = { In: $set, Done: $set, Out: $set };
    \* @type: $set;
    In,
    \* @type: $set;
    Done
\* @type: Seq($state) => Bool;
Seen(hist) == Len(hist) = 0 \/ hist[1].In \subseteq {1}
Init == In = {1} /\ Done = {}
Next == Done' = Done \union In /\ In' = In
Inv == /\ Done \subseteq In
      /\ Seen(<<[In |-> In, Done |-> Done, Out |-> {}]>>)
====
"#;
    assert_eq!(claim(src, "Inv"), Outcome::NoViolationWithin(0));

    // An alias that does not parse is reported, never dropped: dropped,
    // every `$name` naming it reads as an opaque type and the annotation
    // constrains nothing.
    let bad = r#"
---- MODULE BadAlias ----
EXTENDS Integers
\* @typeAlias: set = Set(;
\* @type: $set;
S == {}
Init == TRUE
Next == TRUE
Inv == S = {}
====
"#;
    let err = types_err(bad, "Inv");
    assert!(
        err.contains("@typeAlias `set = Set(` does not parse"),
        "{err}"
    );
}

/// One comment may hold several annotations: `TestReqAckVariants.tla`
/// annotates a variable with a block comment whose first line is the
/// `@typeAlias:` definition and whose third is the variable's own `@type:`.
/// Read as one, the alias's text swallowed the `@type:` line and the
/// variable lost its annotation without a word.
#[test]
fn a_comment_may_hold_an_alias_and_a_type() {
    let src = r#"
---- MODULE BlockAlias ----
EXTENDS Integers, Variants
VARIABLES
    \* @type: Int;
    balance,
    (*
      @typeAlias: MESSAGE = Req({ ask: Int }) | Ack({ success: Bool });

      @type: Set(MESSAGE);
     *)
    msgs,
    (*
      @typeAlias: EVENT = Withdraw(Int) | Lacking(Int);

      @type: Seq(EVENT);
     *)
    log
Init == balance = 100 /\ msgs = {} /\ log = <<>>
Next == UNCHANGED <<balance, msgs, log>>
Inv == msgs = {} /\ log = <<>>
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
            ("balance".to_string(), "Int;".to_string()),
            ("msgs".to_string(), "Set(MESSAGE);".to_string()),
            ("log".to_string(), "Seq(EVENT);".to_string()),
        ],
        "each annotation in the comment binds to the name that follows it"
    );
    let aliases: Vec<(String, String)> = spec
        .type_aliases
        .iter()
        .map(|(k, v)| (k.clone(), v.trim().to_string()))
        .collect();
    assert_eq!(
        aliases,
        vec![
            (
                "MESSAGE".to_string(),
                "Req({ ask: Int }) | Ack({ success: Bool })".to_string()
            ),
            (
                "EVENT".to_string(),
                "Withdraw(Int) | Lacking(Int)".to_string()
            ),
        ],
        "an alias's text ends at the `;` that closes it"
    );
}

/// An annotation on a `LET` definition is checked against that body, not
/// seeded by name: the name is inlined away and never reaches inference,
/// so seeding it can only collide with another `LET` definition of the same
/// name elsewhere. `TestBags.tla` annotates `EB == EmptyBag` as `Int -> Int`
/// in one test and `Str -> Int` in another, and the second refused the spec.
#[test]
fn a_let_scoped_annotation_is_checked_not_seeded() {
    let src = r#"
---- MODULE LetScoped ----
EXTENDS Integers
A == LET \* @type: Int;
        V == 1
    IN V = 1
B == LET \* @type: Str;
        V == "a"
    IN V = "a"
Init == TRUE
Next == TRUE
Inv == /\ A
      /\ B
====
"#;
    assert_eq!(claim(src, "Inv"), Outcome::NoViolationWithin(0));
    // Checked, so an annotation the body contradicts is a type error.
    let wrong = src.replace("V == \"a\"", "V == 2");
    let err = types_err(&wrong, "Inv");
    assert!(err.contains("does not match its body"), "{err}");
    // A variable of the same name keeps its own annotation.
    let shadow = r#"
---- MODULE LetShadow ----
EXTENDS Integers
VARIABLE
    \* @type: Int;
    V
Pick == LET \* @type: Str;
             V == "a"
         IN V = "a"
Init == V = 0
Next == UNCHANGED V
Inv == /\ Pick
      /\ V = 0
====
"#;
    assert_eq!(claim(shadow, "Inv"), Outcome::NoViolationWithin(0));
}

/// An annotation may be written across several `\\*` lines – how
/// `MC_LamportMutexTyped.tla` defines its alias, and `CommentedTypeAnnotation`
/// spreads a type, `//` comments included. Sany hands Apalache a
/// declaration's consecutive comment lines as one text; read line by line
/// here, the first line was an alias with no record to close.
#[test]
fn an_annotation_may_span_several_comment_lines() {
    let src = r#"
---- MODULE Spread ----
EXTENDS Integers, FiniteSets
VARIABLES
  \* the messages in flight, by their type
  \* @typeAlias: message = {
  \*     type: Str,
  \*     clock: Int
  \* };
  \* @type: Set({
  \*   // a comment
  \*   x : Int
  \* });
  v,
  \* @type: Set(message);
  network
Init == v = {} /\ network = {}
Next == UNCHANGED <<v, network>>
Inv == /\ v = {}
      /\ network = {}
====
"#;
    assert_eq!(claim(src, "Inv"), Outcome::NoViolationWithin(0));

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
            (
                "v".to_string(),
                "Set({\n   // a comment\n   x : Int\n });".to_string()
            ),
            ("network".to_string(), "Set(message);".to_string()),
        ],
        "consecutive `\\*` lines are one comment, an annotation binds where it ends"
    );
    assert_eq!(
        spec.type_aliases,
        vec![(
            "message".to_string(),
            "{\n     type: Str,\n     clock: Int\n }".to_string()
        )],
        "an alias defined across lines is one definition"
    );

    // Two annotations on adjacent lines are still two annotations.
    let src = r#"
---- MODULE Adjacent ----
EXTENDS Integers
CONSTANT
  \* @type: Int;
  \* @type: Str;
  c
Init == TRUE
Next == TRUE
Inv == TRUE
====
"#;
    let err = types_err(src, "Inv");
    assert!(err.contains("conflicts"), "{err}");
}

/// A `LET` definition's annotation is checked **out of context**, and a
/// body that reads the enclosing operator's parameters has a shape the
/// context gives it: `s == <<p[1] + d[1], p[2] + d[2]>>` in `move(p, d)`
/// (`SlidingPuzzlesTyped.tla`), checked with `p` and `d` untyped, is
/// ambiguous. That is not an error in the annotation – the main inference
/// types the body where the operator is used – so the check is skipped
/// rather than failed; the first version failed it, exit 120 on a
/// specification the oracle accepts. A contradiction that needs no context
/// is still the type error it is.
#[test]
fn a_let_annotation_that_needs_its_enclosing_parameters_is_not_checked() {
    let src = r#"
---- MODULE OutOfContext ----
EXTENDS Integers
\* @type: (<<Int, Int>>, <<Int, Int>>) => Bool;
Move(p, d) ==
    LET \* @type: <<Int, Int>>;
        s == <<p[1] + d[1], p[2] + d[2]>>
    IN s[1] > 0
VARIABLE x
Init == x = 0
Next == x' = x
Inv == Move(<<1, 2>>, <<3, 4>>)
====
"#;
    assert_eq!(claim(src, "Inv"), Outcome::NoViolationWithin(0));
    let wrong = src.replace("s == <<p[1] + d[1], p[2] + d[2]>>", "s == 1");
    let err = types_err(&wrong, "Inv");
    assert!(
        err.contains("does not match its body") || err.contains("does not check against"),
        "{err}"
    );
}
