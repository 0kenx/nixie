//! Non-literal ranges, structural membership, and range cardinality
//! (issue #22).
//!
//! `a..b` used to demand ground ends — the arena needs to *count* the
//! elements — which blocked every specification whose bound is a `CONSTANT`
//! or arithmetic on one. Membership is a comparison (`a <= x /\ x <= b`),
//! Apalache's own rewrite, and needs nothing of the sort; only a candidate
//! list built *from* a range still needs the ends.

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

// ---- membership over a symbolic range ----

/// The issue's own regression: `x \in 0..(y+1)` with a symbolic `y`, correct
/// in both directions — a membership that holds for every `y`, and one that
/// fails for some `y` and must be reported.
#[test]
fn range_membership_with_a_symbolic_bound() {
    // Holds for every y >= 0: x = 0 is in 0..(y+1) whenever the range is
    // nonempty, and y >= 0 makes it nonempty.
    holds(r"\E y \in 0..3 : 0 \in 0..(y + 1)");
    // And 4 is never in 0..(y+1) for y \in 0..3.
    fails(r"\A y \in 0..3 : 4 \in 0..(y + 1)");
    // An empty range — the TLA+ rule is `a > b` gives `{}`, not an error.
    holds(r"\A e \in 5..3 : FALSE");
}

/// A state variable bounded by a range over a *constant* — the `Nodes == 0..N-1`
/// shape that blocked `EWD840.tla` and ~20 corpus specifications.
#[test]
fn a_state_variable_may_range_over_a_constant() {
    let src = r#"
---- MODULE Ring ----
EXTENDS Integers
CONSTANT N
VARIABLE p
Init == p \in 0..(N - 1)
Next == p' = (p + 1) % N
Inv == p \in 0..(N - 1)
====
"#;
    let cfg = "CONSTANT N = 3\n";
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let config = nixie_tla_syntax::parse_config(cfg).expect("cfg parses");
    let mut tm = TermManager::new();
    let mut bmc = Bmc::prepare_with_config(
        &spec,
        module,
        nixie_tla_check::bmc::Roles {
            init: "Init",
            next: "Next",
            inv: &["Inv"],
            constraints: &[],
        },
        &config,
        &mut tm,
    )
    .expect("prepares");
    assert_eq!(
        bmc.check(4, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(4),
        "the ring stays in bounds forever"
    );
}

// ---- cardinality of a range ----

#[test]
fn range_cardinality_is_arithmetic() {
    holds(r"Cardinality(0..4) = 5");
    // An empty range has zero elements, not an error.
    holds(r"Cardinality(5..3) = 0");
    // And a symbolic bound costs nothing.
    holds(r"\E y \in 0..3 : Cardinality(0..y) = y + 1");
    fails(r"\E y \in 0..3 : Cardinality(0..y) = y");
}

// ---- structural membership over record sets and products ----

/// `r \in [f : S, g : T]` is the conjunction of the field memberships — the
/// cartesian product is never enumerated.
#[test]
fn record_set_membership_is_structural() {
    holds(r"[f |-> 1, g |-> 2] \in [f : {1}, g : {2}]");
    fails(r"[f |-> 1, g |-> 5] \in [f : {1}, g : {2}]");
    // A range as one of the field sets composes.
    holds(r"[f |-> 3, g |-> 2] \in [f : 1..5, g : {2}]");
    fails(r"[f |-> 9, g |-> 2] \in [f : 1..5, g : {2}]");
}

/// `t \in S \X T` is componentwise.
#[test]
fn cartesian_membership_is_componentwise() {
    holds(r"<<1, 2>> \in {1} \X {2}");
    fails(r"<<1, 5>> \in {1} \X {2}");
    holds(r"<<1, 4>> \in {1} \X (3..5)");
    fails(r"<<1, 9>> \in {1} \X (3..5)");
}
