//! Native-mode set comprehensions and `SUBSET` (issue #21).
//!
//! The set theory *is* wired into the solver; what these tests pin is that a
//! comprehension or a powerset is built whenever its base is enumerable – the
//! base's candidate list is the only thing the construction needs – and that
//! membership in `SUBSET T` is decided structurally, with no 2^n expansion.

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

// ======== comprehensions over an enumerable base ========

#[test]
fn a_filter_comprehension_over_a_literal() {
    holds(r"{y \in {1, 2, 3} : y > 5} = {}");
    holds(r"{y \in {1, 2, 3} : y > 1} = {2, 3}");
    // The base need not be a literal: a range is enumerable too.
    holds(r"{y \in 0..4 : y % 2 = 0} = {0, 2, 4}");
}

#[test]
fn a_map_comprehension_over_a_literal() {
    holds(r"{y * 2 : y \in {1, 2, 3}} = {2, 4, 6}");
    // Two elements mapping to the same value are one member.
    holds(r"{y % 2 : y \in {1, 2, 3, 4}} = {0, 1}");
}

/// A comprehension over a **framed** set variable now checks (issue #20's
/// candidate universes): `{y \in s : y > 0} = s` has a real answer. A base
/// with no derivable universe – the pre-frames condition – is still declined
/// by name, never approximated.
#[test]
fn a_comprehension_over_a_framed_base_checks() {
    let src = r#"
---- MODULE Sym ----
EXTENDS Integers
VARIABLE s
Init == s = {1}
Next == UNCHANGED s
Inv  == {y \in s : y > 0} = s
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc = Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm)
        .expect("the framed set has a candidate universe, so this encodes");
    assert_eq!(
        bmc.check(0, &mut tm).expect("checks"),
        nixie_tla_check::bmc::Outcome::NoViolationWithin(0)
    );
}

// ======== SUBSET ========

/// Membership in a powerset is subset-or-equal, decided by the set theory
/// with no expansion at all.
#[test]
fn membership_in_a_powerset_is_structural() {
    holds(r"{1} \in SUBSET {1, 2}");
    holds(r"{} \in SUBSET {1, 2}");
    holds(r"{1, 2} \in SUBSET {1, 2}");
    fails(r"{3} \in SUBSET {1, 2}");
    fails(r"{1, 3} \in SUBSET {1, 2}");
}

/// `SUBSET` as a *value* enumerates 2^n under the candidate budget, and a
/// quantifier over it sees every subset exactly as cardinality would.
#[test]
fn a_powerset_as_a_value_enumerates() {
    // Exactly the subsets of {1, 2} contain 2: {2} and {1, 2}.
    holds(r"Cardinality({S \in SUBSET {1, 2} : 2 \in S}) = 2");
    // And no subset of {1, 2} contains 3 – the issue's own regression.
    fails(r"\E S \in SUBSET {1, 2} : 3 \in S");
    holds(r"\E S \in SUBSET {1, 2} : 1 \in S /\ 2 \in S");
}

/// A set-valued state variable's membership in `SUBSET` composes with the
/// transition relation's set operations: the base stays a term and the
/// membership is a set-theory constraint.
#[test]
fn a_state_variable_may_be_a_subset_of_a_range() {
    let src = r#"
---- MODULE InPow ----
EXTENDS Integers
VARIABLE S
Init == S \in SUBSET (1..3) /\ 2 \notin S
Next == S' = S \cup {2}
Inv == 2 \notin S
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert_eq!(
        bmc.check(1, &mut tm).expect("checks"),
        Outcome::Violation { step: 1 }
    );
}
