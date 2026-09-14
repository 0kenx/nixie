//! Sequences: `<<>>`, `Append`, `Len`, `Head`, and equality.
//!
//! A sequence is a **length and a graph** — a datatype holding an `Int` and an
//! array from `1..` — which is what TLA+ says a sequence is (a function on
//! `1..Len(s)`) with the length carried alongside, because an array alone
//! cannot say where the sequence stops.
//!
//! It has *two* shapes here, and that is the thing to keep straight. `<<a, b>>`
//! is a tuple and a sequence at once — TLA+ does not distinguish them — so a
//! literal encodes structurally while a `VARIABLE` of sequence type encodes to
//! the datatype. The operators take either, the same way the set operators
//! dispatch on a set's representation rather than on a mode. An operator that
//! only understood the datatype declined `Len(<<"a", "b">>)`, which is how
//! this came up: `tla-connect`'s post-hoc trace validation generates exactly
//! that.

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome};

fn claim(vars: &str, init: &str, body: &str) -> Outcome {
    let src = format!(
        r"
---- MODULE Claim ----
EXTENDS Integers, Sequences
VARIABLE {vars}
Init == {init}
Next == UNCHANGED <<{vars}>>
Inv  == {body}
====
"
    );
    let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
    let loaded = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = loaded.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&loaded, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    bmc.check(0, &mut tm).expect("checks")
}

fn holds(vars: &str, init: &str, body: &str) {
    assert_eq!(
        claim(vars, init, body),
        Outcome::NoViolationWithin(0),
        "`{body}`"
    );
}

fn fails(vars: &str, init: &str, body: &str) {
    assert_eq!(
        claim(vars, init, body),
        Outcome::Violation { step: 0 },
        "`{body}`"
    );
}

// ---- a literal sequence, which is structurally a tuple ----

#[test]
fn len_of_a_literal() {
    holds("x", "x = 0", r#"Len(<<"a", "b">>) = 2"#);
    fails("x", "x = 0", r#"Len(<<"a", "b">>) = 3"#);
}

#[test]
fn len_of_the_empty_literal() {
    holds("x", "x = 0", "Len(<<>>) = 0");
    fails("x", "x = 0", "Len(<<>>) = 1");
}

#[test]
fn append_to_a_literal() {
    holds("x", "x = 0", r#"Len(Append(<<"a">>, "b")) = 2"#);
    holds("x", "x = 0", r#"Append(<<1>>, 2) = <<1, 2>>"#);
    fails("x", "x = 0", r#"Append(<<1>>, 2) = <<1, 3>>"#);
}

#[test]
fn head_of_a_literal() {
    holds("x", "x = 0", "Head(<<7, 8>>) = 7");
    fails("x", "x = 0", "Head(<<7, 8>>) = 8");
}

// ---- a sequence-valued state variable, which is the datatype ----

/// The shape every specification `intent` generates is built on:
/// `history = <<>>` then `history' = Append(history, …)`, with the invariant
/// tying the length to a counter.
#[test]
fn a_sequence_variable_grows_by_append() {
    let src = r#"
---- MODULE Grow ----
EXTENDS Integers, Sequences
VARIABLES h, pc
Init == h = <<>> /\ pc = 0
Next == h' = Append(h, "x") /\ pc' = pc + 1
Inv  == Len(h) = pc
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let loaded = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = loaded.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&loaded, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert_eq!(
        bmc.check(4, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(4),
        "`Len(h) = pc` is an invariant of growing one per step"
    );
}

/// And a claim that is *false* about the same specification is found, so the
/// one above is not passing because nothing is constrained.
#[test]
fn a_false_claim_about_a_growing_sequence_is_found() {
    let src = r#"
---- MODULE GrowBad ----
EXTENDS Integers, Sequences
VARIABLES h, pc
Init == h = <<>> /\ pc = 0
Next == h' = Append(h, "x") /\ pc' = pc + 1
Inv  == Len(h) < 2
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let loaded = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = loaded.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&loaded, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert_eq!(
        bmc.check(4, &mut tm).expect("checks"),
        Outcome::Violation { step: 2 }
    );
}

/// The empty sequence a `VARIABLE` is pinned to compares equal to the literal
/// `<<>>`, which is what makes `h = <<>>` in `Init` mean anything. Both are
/// built over the same shared base array; two empty sequences over different
/// bases would compare unequal, because the datatype's equality looks at the
/// array past the length as well.
#[test]
fn an_empty_sequence_variable_equals_the_empty_literal() {
    let src = r"
---- MODULE Empty ----
EXTENDS Integers, Sequences
VARIABLE h
Init == h = <<>>
Next == UNCHANGED h
Inv  == Len(h) = 0
====
";
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let loaded = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = loaded.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&loaded, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert_eq!(
        bmc.check(2, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(2)
    );
}
