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

// ---- Tail and concatenation ----

/// `Tail` moves the sequence's **window** forward instead of copying: `s[i]`
/// is `fun[off + i]`, so shortening from the front costs nothing and needs no
/// quantifier. Apalache carries a start and an end on its proto-sequence for
/// the same reason.
#[test]
fn tail_of_a_literal() {
    holds("x", "x = 0", "Tail(<<1, 2, 3>>) = <<2, 3>>");
    holds("x", "x = 0", "Len(Tail(<<1, 2, 3>>)) = 2");
    holds("x", "x = 0", "Head(Tail(<<1, 2, 3>>)) = 2");
}

#[test]
fn concatenation_of_literals() {
    holds("x", "x = 0", "<<1, 2>> \\o <<3>> = <<1, 2, 3>>");
    holds("x", "x = 0", "Len(<<1>> \\o <<2, 3>>) = 3");
    fails("x", "x = 0", "<<1, 2>> \\o <<3>> = <<1, 2>>");
}

/// A queue drained by `Tail` and filled by `\o`, which is the pattern every
/// generated specification with a channel uses.
#[test]
fn a_queue_is_drained_and_filled() {
    let src = r#"
---- MODULE Queue ----
EXTENDS Integers, Sequences
VARIABLES q, n
Init == q = <<>> /\ n = 0
Next == \/ (Len(q) = 0 /\ q' = q \o <<"a", "b">> /\ n' = n + 2)
        \/ (Len(q) > 0 /\ q' = Tail(q) /\ n' = n - 1)
Inv  == Len(q) >= 0
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
        Outcome::NoViolationWithin(4)
    );
}

/// A queue of **records**, which is what a generated channel actually holds.
/// The elements arrive structural — field by field — and are reified into
/// their datatype on the way in.
#[test]
fn a_queue_of_records() {
    let src = r#"
---- MODULE RecQueue ----
EXTENDS Integers, Sequences
VARIABLE q
Init == q = <<>>
Next == q' = q \o <<[type |-> "Log", arg0 |-> "first"]>>
Inv  == Len(q) < 2
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
    let t = bmc.counterexample().expect("a decoded trace");
    assert_eq!(t.states.len(), 3, "{t}");
}

/// A sequence is indexed through the window too, and the index need not be a
/// literal — `events[Len(events)]` is how a specification reads the last thing
/// that happened.
#[test]
fn a_sequence_is_indexed_by_a_computed_position() {
    holds("x", "x = 0", "<<10, 20, 30>>[Len(<<1, 2>>)] = 20");
}

/// Sharing one `Seq` between an operator's argument and its result reads as
/// "these have the same type" — true, until a tuple is involved. `<<a, b, c>>`
/// is a tuple *and* a sequence, and unifying keeps the tuple because it is the
/// more precise shape of a literal; that precision then propagates backwards
/// and makes the queue a 3-tuple, which has no sequence operations at all.
#[test]
fn concatenating_a_literal_does_not_fix_the_queue_length() {
    let src = r#"
---- MODULE Growing ----
EXTENDS Integers, Sequences
VARIABLE q
Init == q = <<>>
Next == q' = q \o <<"x", "y", "z">>
Inv  == Len(q) < 7
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let loaded = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = loaded.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&loaded, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    // 0, 3, 6, 9 — the ninth breaks it, which needs the queue to have grown
    // three times rather than been pinned to three elements.
    assert_eq!(
        bmc.check(4, &mut tm).expect("checks"),
        Outcome::Violation { step: 3 }
    );
}

// ---- an invariant must be a predicate ----

/// `Inv == (100 - 10) + 5` is a perfectly good constant-level expression and a
/// perfectly useless invariant. TLA+'s level rules do not catch it, and
/// negating a non-Boolean and finding the result satisfiable would report a
/// violation for a specification that never stated a property. `intent`'s
/// compiler emits exactly this when a `.intent` file gives an invariant an
/// arithmetic body.
#[test]
fn a_non_boolean_invariant_is_refused() {
    let src = r"
---- MODULE NotAPredicate ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Inv  == LET a == 100 b == 10 IN (a - b) + 5
====
";
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let loaded = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = loaded.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let err = Bmc::prepare(&loaded, module, "Init", "Next", "Inv", &[], &mut tm)
        .err()
        .map(|e| e.to_string())
        .unwrap_or_default();
    assert!(err.contains("BOOLEAN"), "{err}");
}

// ---- SubSeq ----

/// `SubSeq(s, m, n)` moves the window and resizes it — element `i` of the
/// result is element `m + i - 1` of `s`. Nothing is copied, for the same
/// reason `Tail` copies nothing, and `Tail` is exactly `SubSeq(s, 2, Len(s))`.
#[test]
fn subseq_of_a_literal() {
    holds("x", "x = 0", "SubSeq(<<1, 2, 3, 4>>, 2, 3) = <<2, 3>>");
    holds("x", "x = 0", "Len(SubSeq(<<1, 2, 3, 4>>, 2, 3)) = 2");
    holds("x", "x = 0", "SubSeq(<<1, 2, 3>>, 1, 3) = <<1, 2, 3>>");
    fails("x", "x = 0", "SubSeq(<<1, 2, 3, 4>>, 2, 3) = <<2, 3, 4>>");
}

/// An empty range is the empty sequence, not an error.
#[test]
fn an_empty_subseq() {
    holds("x", "x = 0", "SubSeq(<<1, 2, 3>>, 3, 2) = <<>>");
    holds("x", "x = 0", "Len(SubSeq(<<1, 2, 3>>, 3, 2)) = 0");
}

/// On a sequence-valued variable, where the bounds may be symbolic: they are
/// arithmetic on the offset and the length, not a count of anything that has
/// to be enumerated.
#[test]
fn subseq_of_a_variable_with_symbolic_bounds() {
    let src = r#"
---- MODULE Sub ----
EXTENDS Integers, Sequences
VARIABLES h, n
Init == h = <<>> /\ n = 2
Next == h' = Append(Append(Append(h, "a"), "b"), "c") /\ UNCHANGED n
Inv  == Len(h) = 0 \/ Len(SubSeq(h, n, Len(h))) = 2
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let loaded = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = loaded.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&loaded, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert_eq!(
        bmc.check(1, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(1)
    );
}

/// And `Tail` agrees with the `SubSeq` that means the same thing.
#[test]
fn tail_agrees_with_subseq() {
    holds(
        "x",
        "x = 0",
        "Tail(<<1, 2, 3>>) = SubSeq(<<1, 2, 3>>, 2, 3)",
    );
}
