//! `CHOOSE` and `^` (issue #24).
//!
//! `CHOOSE x \in S : P` is `set.choose` over the native filter `{x \in S :
//! P}` — the set theory owns the semantics, so **congruence gives TLA+'s
//! determinism exactly**: extensionally equal filters give the same value,
//! and an empty filter leaves it unconstrained but consistent, which is the
//! one thing TLA+ promises. `CHOOSE x : x \notin S` (the fresh-value idiom)
//! is one shared constant per set, constrained outside it. `^` with a ground
//! exponent is an unfolded product — exact and replayable; anything else is
//! declined by name.

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome};

fn claim(body: &str) -> Outcome {
    let src = format!(
        r#"
---- MODULE Claim ----
EXTENDS Integers, FiniteSets
VARIABLE x
NoVal(S) == CHOOSE v : v \notin S
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
NoVal(S) == CHOOSE v : v \notin S
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

// ---- bounded CHOOSE ----

/// The issue's own regression: `CHOOSE` over `{1,2}` and over `{2,1}` — the
/// same set written in two orders — must give the same value, which is
/// TLA+'s determinism requirement and comes free from congruence over the
/// set theory's extensional equality.
#[test]
fn choose_is_deterministic_across_set_order() {
    holds(r"(CHOOSE x \in {1, 2} : TRUE) = (CHOOSE y \in {2, 1} : TRUE)");
}

/// The value is one of the filter's members, and the filter is respected.
#[test]
fn choose_respects_the_filter() {
    holds(r"(CHOOSE x \in {1, 3, 5} : x > 2) \in {3, 5}");
    // ...and it is a member of the underlying set at all.
    holds(r"(CHOOSE x \in {1, 3, 5} : x > 2) \in {1, 3, 5}");
}

/// An empty filter leaves the value unconstrained but **fixed**: the same
/// term is the same value, and nothing else is claimed about it.
#[test]
fn choose_over_an_empty_filter_is_still_a_value() {
    holds(r"(CHOOSE x \in {} : TRUE) = (CHOOSE y \in {} : TRUE)");
}

// ---- the fresh-value idiom ----

/// `CHOOSE x : x \notin S` — one constant, outside `S`, and the *same*
/// constant wherever the idiom is written over the same set.
#[test]
fn the_fresh_value_idiom_is_outside_and_stable() {
    holds(r"LET S == {1, 2} IN NoVal(S) # 1 /\ NoVal(S) # 2");
    // The same idiom over the same set is one value: two spellings agree.
    holds(r"(CHOOSE x : x \notin {1, 2}) = (CHOOSE y : y \notin {2, 1})");
}

/// A helper used above: the idiom spelled as an operator, so the tests read
/// the way specifications write it.
#[test]
fn the_fresh_value_idiom_as_an_operator() {
    // Defined inline in the body; see the helper in the module.
    holds(r"NoVal({1, 2}) \notin {1, 2}");
}

// ---- `^` ----

#[test]
fn a_ground_exponent_is_a_product() {
    holds(r"2 ^ 10 = 1024");
    holds(r"3 ^ 0 = 1");
    holds(r"5 ^ 1 = 5");
    holds(r"(0 - 2) ^ 2 = 4");
    fails(r"2 ^ 10 = 1023");
}

/// A symbolic exponent is non-linear and declined by name — an
/// uninterpreted function whose models nothing could replay would be a
/// guess with extra steps, and the replay gate would refuse its traces
/// anyway.
#[test]
fn a_symbolic_exponent_declines() {
    declines(r"\E y \in 1..3 : 2 ^ y = 8");
}

/// A negative exponent is undefined in TLA+.
#[test]
fn a_negative_exponent_declines() {
    declines(r"2 ^ (0 - 1) = 0");
}
