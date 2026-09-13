//! TLC's tracing and assertion operators, encoded as `TLC.tla` defines them.
//!
//! ```tla
//! Print(out, val)  == val
//! PrintT(out)      == TRUE
//! Assert(val, out) == IF val = TRUE THEN TRUE ELSE CHOOSE v : TRUE
//! ```
//!
//! `Print` and `PrintT` are unambiguous: they exist for a side effect a
//! symbolic encoding has no business reproducing, and their *value* is written
//! down exactly. `Assert` is the interesting one. Its `ELSE` branch is
//! `CHOOSE v : TRUE` — a value TLA+ leaves unspecified — so a failing `Assert`
//! does not have the value `FALSE`, and encoding it as `FALSE` would report a
//! violation the specification does not have. It is encoded as a single shared
//! free Boolean, which is what "unspecified" means.
//!
//! What that buys is the right reading of a failing `Assert` in an invariant.
//! The free Boolean is chosen by the solver *within the query*, so
//! `Violation` comes to mean "there is a behaviour, and a reading of the
//! unspecified value, under which the invariant fails" — which is exactly a
//! failure to establish the invariant, and it is the same thing TLC reports by
//! halting. The asymmetry is the one the rest of the encoder keeps:
//! a `Violation` may be spurious, `NoViolationWithin` stays sound.

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome};

fn claim(vars: &str, init: &str, body: &str) -> Outcome {
    let src = format!(
        r"
---- MODULE Claim ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE {vars}
Init == {init}
Next == UNCHANGED <<{vars}>>
Inv  == {body}
====
"
    );
    let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
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

// ---- Print is the identity on its second argument ----

#[test]
fn print_returns_its_value() {
    holds("x", "x = 3", r#"Print("tracing", x = 3)"#);
}

#[test]
fn print_does_not_make_a_false_claim_true() {
    fails("x", "x = 3", r#"Print("tracing", x = 4)"#);
}

#[test]
fn print_of_a_non_boolean_is_that_value() {
    holds("x", "x = 3", r#"Print("tracing", x) = 3"#);
}

/// The message is not encoded at all. It cannot reach the value, so a
/// specification must not be declined because of what it would have printed —
/// here a set, which in a value position the encoder would otherwise refuse.
#[test]
fn the_message_is_not_encoded() {
    holds("x", "x = 3", r"Print({1, 2, 3}, x = 3)");
}

#[test]
fn print_nests() {
    holds("x", "x = 3", r#"Print("a", Print("b", x)) = 3"#);
}

// ---- PrintT is TRUE ----

#[test]
fn print_t_is_true() {
    holds("x", "x = 3", r#"PrintT("tracing")"#);
}

#[test]
fn print_t_is_true_even_as_a_conjunct() {
    holds("x", "x = 3", r#"PrintT("tracing") /\ x = 3"#);
    fails("x", "x = 3", r#"PrintT("tracing") /\ x = 4"#);
}

// ---- Assert ----

/// The `THEN` branch is pinned: a holding `Assert` is `TRUE`, not unspecified.
#[test]
fn a_holding_assert_is_true() {
    holds("x", "x = 3", r#"Assert(x = 3, "x is 3")"#);
}

/// A failing `Assert` in an invariant is reported. Not because the encoding
/// reads `CHOOSE v : TRUE` as `FALSE` — it does not — but because the value is
/// unspecified, so the solver is free to read it as `FALSE`, and a `Violation`
/// here means "the specification does not establish this invariant". That is
/// the honest claim, and it is what TLC reports by halting.
#[test]
fn a_failing_assert_in_an_invariant_is_reported() {
    fails("x", "x = 3", r#"Assert(x = 4, "x is not 4")"#);
}

/// What the shared free Boolean must not do is bless a *conjunction*: the
/// unspecified value stands only for the failing `Assert` itself.
#[test]
fn an_assert_does_not_bless_its_context() {
    fails("x", "x = 3", r#"Assert(x = 3, "ok") /\ x = 4"#);
}

/// `CHOOSE` picks the same value wherever it is written, so two failing
/// `Assert`s cannot be read two ways at once. `A \/ ~A` over one shared name
/// is a tautology; over two independent names it is not, and the solver would
/// be free to falsify this.
#[test]
fn every_choose_is_the_same_value() {
    holds("x", "x = 3", r#"Assert(x = 4, "a") \/ ~Assert(x = 4, "b")"#);
}

#[test]
fn assert_is_true_when_the_condition_is_a_tautology() {
    holds("x", "x = 3", r#"Assert(x = 3 \/ x # 3, "always") "#);
}

/// The other direction is the one that would be unsound. A failing `Assert` in
/// `Init` must not *prune* the state: `x = 3` is still reachable, so an
/// invariant it violates is still reported. Reading the unspecified value as
/// `FALSE` would delete the state and hide the counterexample.
#[test]
fn a_failing_assert_in_init_does_not_prune_the_state() {
    fails("x", r#"x = 3 /\ Assert(x = 4, "no") "#, "x # 3");
}
