//! Positive-existential skolemization over the standard infinite sets
//! (issue #20, first piece).
//!
//! `\E x \in Nat : P(x)` in a position the solver is asked to **satisfy**
//! becomes a fresh constant with `x \in Nat /\ P(x)`. Polarity is the
//! soundness boundary: an existential under an odd number of negations is a
//! universal claim and must NOT be skolemized, while a *universal* under an
//! odd number of negations is an existential and may be.

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome};

fn claim(body: &str) -> Outcome {
    let src = format!(
        r#"
---- MODULE Claim ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x = 0
Next == UNCHANGED <<x>>
Inv  == {body}
====
"#
    );
    let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    bmc.check(0, &mut tm).expect("checks")
}

fn holds(body: &str) {
    assert_eq!(claim(body), Outcome::NoViolationWithin(0), "`{body}`");
}

fn fails(body: &str) {
    assert_eq!(claim(body), Outcome::Violation { step: 0 }, "`{body}`");
}

fn declines(body: &str) {
    let src = format!(
        r#"
---- MODULE Claim ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x = 0
Next == UNCHANGED <<x>>
Inv  == {body}
====
"#
    );
    let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert!(bmc.check(0, &mut tm).is_err(), "`{body}` should decline");
}

// ======== positive existentials, in an asserted formula ========

/// The witness idiom where it is genuinely one: `Init`'s existential. The
/// helper spec's `Init` is fixed, so the body here restates a witness form
/// as an invariant's *dual* instead; the direct form lives in the next test.
#[test]
fn a_positive_existential_over_nat_skolemizes() {
    // A **negated** existential in the invariant is the query's positive
    // existential (`~~E` in `~Inv`): skolemized and answered. `~\E y \in
    // Nat : y < x` holds – no natural is below zero.
    holds(r"~\E y \in Nat : y < x");
    // A negated existential over STRING, through the same shape.
    holds(r#"~\E s \in STRING : s # s"#);
}

/// A positive existential in `Init` is witnessed: an initial state exists
/// exactly when the witness and its membership do.
#[test]
fn a_witness_in_init_is_skolemized() {
    let src = r#"
---- MODULE Wit ----
EXTENDS Integers
VARIABLE x
Init == \E y \in Nat : x = y + 1
Next == UNCHANGED x
Inv == x >= 1
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert_eq!(
        bmc.check(0, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(0),
        "the witness y = 0 gives x = 1"
    );
}

// ======== polarity ========

/// An existential under a negation is a universal: `~\E y \in Nat : y < x`
/// with `x = 0` **holds**, and skolemizing it would answer the opposite.
/// A **plain positive** existential in the invariant is the query's
/// *universal* (`~Inv` doubles the negation), which no skolem can serve:
/// declined rather than enumerated over a guessed bound.
#[test]
fn a_plain_positive_existential_in_an_invariant_declines() {
    declines(r"\E y \in Nat : y > x");
}

/// A **positive** universal in the invariant is the query's existential
/// (the invariant enters negated), so it skolemizes: `\A y \in Nat : y >
/// x` at `x = 0` is refuted by the witness `y = 0`.
#[test]
fn an_invariants_universal_skolemizes_as_the_query_existential() {
    fails(r"\A y \in Nat : y > x");
    // ...and the true universal claim now holds, witnessed:
    holds(r"\A y \in Nat : y >= 0");
}

/// A negated implication arm flips polarity: in the invariant, `~(x < 0
/// => \A y \in Nat : y > x)`'s universal sits under two negations and the
/// claim is decidable via the finite reading; the infinite-set existential
/// arm of an implication in an *invariant* is the query's universal and
/// declines – pinned here so nobody "fixes" it into a wrong answer.
#[test]
fn implication_arms_carry_polarity() {
    // The antecedent false makes the implication true at x = 0; the
    // universal arm under the implication's flipped polarity is the
    // query's existential only when the arm is the *negated* one.
    holds(r"x < 0 => \A y \in {0, 1} : y >= 0");
    declines(r"x < 0 => \E y \in Nat : y < x");
}

/// An `IF` condition is both-polarity: an existential inside one is never
/// rewritten, and the encoding declines rather than guessing.
#[test]
fn ite_conditions_are_never_rewritten() {
    declines(r"IF \E y \in Nat : y < x THEN TRUE ELSE FALSE");
}
