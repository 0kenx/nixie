//! TLA+ functions: a domain and a graph.
//!
//! A function value carries both halves (`arena::Value::Fun`). The graph is an
//! SMT array — `f[x]` a select, `[f EXCEPT ![i] = v]` a store — and the domain
//! is a set-sorted term, which is what an array on its own cannot hold.
//!
//! Carrying the domain is not a refinement, it closes a hole: array equality
//! compares every index, so `[x \in {1} |-> 0]` and `[x \in {1, 2} |-> 0]`
//! are reported *equal* whenever the array happens to agree at 2. That is the
//! direction that hides a counterexample, and
//! `different_domains_are_different_functions` is its regression.

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome};

/// Check `claim` in the initial state: `Violation { step: 0 }` means false,
/// `NoViolationWithin(0)` means true.
fn claim(body: &str) -> Outcome {
    let src = format!(
        r"
---- MODULE Claim ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x = 0
Next == x' = x
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

fn holds(body: &str) {
    assert_eq!(claim(body), Outcome::NoViolationWithin(0), "`{body}`");
}

fn fails(body: &str) {
    assert_eq!(claim(body), Outcome::Violation { step: 0 }, "`{body}`");
}

// ---- the graph ----

#[test]
fn a_function_takes_the_value_its_body_gives() {
    holds("[i \\in {1, 2} |-> i + 10][1] = 11");
    holds("[i \\in {1, 2} |-> i + 10][2] = 12");
}

#[test]
fn a_wrong_value_is_reported() {
    fails("[i \\in {1, 2} |-> i + 10][1] = 12");
}

#[test]
fn a_function_over_a_range_is_enumerated() {
    holds("[i \\in 1..3 |-> i * i][3] = 9");
}

// ---- the domain ----

#[test]
fn domain_is_exact() {
    holds("DOMAIN [i \\in {1, 2} |-> 0] = {1, 2}");
    fails("DOMAIN [i \\in {1, 2} |-> 0] = {1, 2, 3}");
}

#[test]
fn domain_cardinality_is_exact() {
    holds("Cardinality(DOMAIN [i \\in 1..4 |-> 0]) = 4");
}

#[test]
fn membership_in_the_domain_is_decided() {
    holds("2 \\in DOMAIN [i \\in {1, 2} |-> 0]");
    holds("3 \\notin DOMAIN [i \\in {1, 2} |-> 0]");
}

// ---- equality ----

/// The regression for the hole carrying the domain closes. Both functions are
/// 0 at 1; they differ only in whether 2 is in the domain, which is invisible
/// to array equality.
#[test]
fn different_domains_are_different_functions() {
    fails("[i \\in {1} |-> 0] = [i \\in {1, 2} |-> 0]");
}

/// ...and the other direction, which is what the shared base array buys: two
/// separately-built functions with the same domain and the same values must
/// come out equal, even though each is its own chain of stores.
#[test]
fn the_same_function_written_twice_is_equal() {
    holds("[i \\in {1, 2} |-> i + 1] = [i \\in {1, 2} |-> i + 1]");
}

#[test]
fn functions_differing_at_a_point_are_unequal() {
    fails("[i \\in {1, 2} |-> 0] = [i \\in {1, 2} |-> IF i = 2 THEN 1 ELSE 0]");
}

// ---- EXCEPT ----

#[test]
fn except_replaces_one_point_and_keeps_the_rest() {
    holds("[[i \\in {1, 2} |-> 0] EXCEPT ![1] = 5][1] = 5");
    holds("[[i \\in {1, 2} |-> 0] EXCEPT ![1] = 5][2] = 0");
}

/// `EXCEPT` never extends a function, so the domain is untouched.
#[test]
fn except_keeps_the_domain() {
    holds("DOMAIN [[i \\in {1, 2} |-> 0] EXCEPT ![1] = 5] = {1, 2}");
}

// ---- the function set ----

#[test]
fn a_function_set_states_a_type() {
    holds("[i \\in {1, 2} |-> 0] \\in [{1, 2} -> {0, 7}]");
    // The domain has to match, not merely be contained.
    fails("[i \\in {1, 2} |-> 0] \\in [{1, 2, 3} -> {0, 7}]");
    // ...and so does every value.
    fails("[i \\in {1, 2} |-> 0] \\in [{1, 2} -> {7}]");
}

/// `Nat` as a codomain goes through the same `\in` dispatch as anywhere else,
/// so it becomes `>= 0` rather than an unconstrained opaque set.
#[test]
fn a_function_into_nat_is_stated_not_declined() {
    holds("[i \\in {1, 2} |-> i] \\in [{1, 2} -> Nat]");
    fails("[i \\in {1, 2} |-> 0 - i] \\in [{1, 2} -> Nat]");
}

// ---- a function-typed state variable ----

/// The shape the whole exercise is for: a function variable given its value by
/// a constructor in `Init` and updated by `EXCEPT` in `Next`.
const REGISTER: &str = r"
---- MODULE Register ----
EXTENDS Integers
VARIABLE f
Init == f = [i \in 1..3 |-> 0]
Next == f' = [f EXCEPT ![1] = f[1] + 1]
Inv  == f[1] < 2
====
";

#[test]
fn a_function_variable_is_checked_across_steps() {
    let parsed = nixie_tla_syntax::parse_file(REGISTER).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    // `f[1]` is 0, 1, 2 — so `f[1] < 2` first fails at step 2.
    assert_eq!(
        bmc.check(5, &mut tm).expect("checks"),
        Outcome::Violation { step: 2 }
    );
}

/// The untouched points of a function variable stay put across a step.
const UNTOUCHED: &str = r"
---- MODULE Untouched ----
EXTENDS Integers
VARIABLE f
Init == f = [i \in 1..3 |-> 0]
Next == f' = [f EXCEPT ![1] = 1]
Inv  == f[2] = 0
====
";

#[test]
fn except_leaves_the_other_points_alone() {
    let parsed = nixie_tla_syntax::parse_file(UNTOUCHED).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert_eq!(
        bmc.check(4, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(4)
    );
}

// ---- quantifying over a set that is now a term ----
//
// `DOMAIN f` is a set-sorted term, and a bounded quantifier is *instantiated*
// per candidate — so the candidates have to be readable back off the term.
// Every set this encoder builds is a union of (conditional) singletons, which
// is exactly what `Encoder::candidates_of` inverts.

#[test]
fn a_quantifier_ranges_over_a_function_domain() {
    holds("\\A i \\in DOMAIN [j \\in {1, 2} |-> j * 2] : i < 3");
    fails("\\A i \\in DOMAIN [j \\in {1, 2} |-> j * 2] : i < 2");
}

#[test]
fn an_existential_ranges_over_a_function_domain() {
    holds("\\E i \\in DOMAIN [j \\in 1..4 |-> 0] : i = 3");
    fails("\\E i \\in DOMAIN [j \\in 1..4 |-> 0] : i = 9");
}

/// The classic shape: every value a function takes on its domain.
#[test]
fn a_quantifier_reaches_the_values_too() {
    holds("\\A i \\in DOMAIN [j \\in 1..3 |-> j + 1] : [j \\in 1..3 |-> j + 1][i] > 1");
}

/// A genuinely opaque set — a state variable — has no candidate list, and is
/// refused by that name rather than approximated.
#[test]
fn an_opaque_set_has_no_candidate_list() {
    let src = r"
---- MODULE Opaque ----
EXTENDS Integers
VARIABLE s
Init == s = {1, 2}
Next == s' = s
Inv  == \A i \in s : i < 3
====
";
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let err =
        nixie_tla_check::bmc::Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm)
            .err();
    // Either it prepares and the quantifier is declined at encode time, or it
    // is declined here — what must not happen is a candidate list being
    // invented for a variable whose members the transition relation decides.
    if err.is_none() {
        let mut bmc =
            nixie_tla_check::bmc::Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm)
                .expect("prepares");
        let out = bmc.check(1, &mut tm);
        assert!(
            out.is_err(),
            "a quantifier over a set variable must be declined, got {out:?}"
        );
    }
}

// ---- a tuple is a function on `1..n` ----
//
// TLA+ has no separate sequence type, so the two spellings denote one value.
// The evaluator normalises them into one representation; the encoder cannot,
// because a function-typed state variable has no candidate list to turn into
// a tuple — so `arena::eq_values` crosses the two by the definition instead.

#[test]
fn a_tuple_equals_the_function_on_its_indices() {
    holds("<<2, 4, 6>> = [i \\in 1..3 |-> 2 * i]");
    holds("[i \\in 1..3 |-> 2 * i] = <<2, 4, 6>>");
}

#[test]
fn a_different_value_makes_them_unequal() {
    fails("<<2, 4, 7>> = [i \\in 1..3 |-> 2 * i]");
}

/// A different domain is a different function, tuple or not.
#[test]
fn a_shorter_tuple_is_not_the_same_function() {
    fails("<<2, 4>> = [i \\in 1..3 |-> 2 * i]");
    fails("<<2, 4, 6>> = [i \\in 2..4 |-> 2 * i]");
}
