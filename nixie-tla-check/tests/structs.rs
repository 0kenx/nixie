//! Tuples and records as single-constructor datatypes.
//!
//! They used to be **structural only**: taken apart by the encoder before
//! anything reached the solver, with no SMT sort of their own. The stated
//! reason was that an SMT array forces one sort across every index, so
//! `<<1, "a">>` could not be array-backed — which is true, and does not apply
//! to a datatype, where each field carries its own sort. Z3 and CVC5 model
//! them this way.
//!
//! Having a sort is what a set of tuples and a record-valued state variable
//! need in order to exist at all; it was the single largest cause on the
//! blocked list (61 specifications across `Set`, `function` and `record`).
//!
//! The structural form has not gone away. It is still what makes a literal
//! index and an exact `DOMAIN` work; the datatype is what a value reifies
//! *into* when something needs one term.

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome};

fn claim(vars: &str, init: &str, body: &str) -> Outcome {
    let src = format!(
        r"
---- MODULE Claim ----
EXTENDS Integers, FiniteSets
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

// ---- a record-valued state variable ----

#[test]
fn a_record_variable_has_a_sort() {
    holds("r", "r = [a |-> 1, b |-> 2]", "r.a = 1 /\\ r.b = 2");
    fails("r", "r = [a |-> 1, b |-> 2]", "r.a = 2");
}

/// Heterogeneous fields, which is the case an array-backed record could never
/// have had.
#[test]
fn a_record_may_mix_field_types() {
    holds(
        "r",
        "r = [n |-> 1, s |-> \"x\", b |-> TRUE]",
        "r.n = 1 /\\ r.s = \"x\" /\\ r.b",
    );
}

#[test]
fn record_equality_is_field_by_field() {
    holds("r", "r = [a |-> 1, b |-> 2]", "r = [a |-> 1, b |-> 2]");
    fails("r", "r = [a |-> 1, b |-> 2]", "r = [a |-> 1, b |-> 3]");
}

/// `EXCEPT` on a reified record rebuilds the constructor with one field
/// replaced, and leaves the others alone.
#[test]
fn except_on_a_record_variable() {
    holds("r", "r = [a |-> 1, b |-> 2]", "[r EXCEPT !.a = 9].a = 9");
    holds("r", "r = [a |-> 1, b |-> 2]", "[r EXCEPT !.a = 9].b = 2");
    holds(
        "r",
        "r = [a |-> 1, b |-> 2]",
        "[r EXCEPT !.a = 9] = [a |-> 9, b |-> 2]",
    );
}

/// The field names are in the datatype declaration, so `DOMAIN` stays exact
/// even once the value is a term.
#[test]
fn domain_of_a_record_variable() {
    holds("r", "r = [a |-> 1, b |-> 2]", "DOMAIN r = {\"a\", \"b\"}");
    holds("r", "r = [a |-> 1, b |-> 2]", "\"a\" \\in DOMAIN r");
    holds("r", "r = [a |-> 1, b |-> 2]", "\"c\" \\notin DOMAIN r");
}

// ---- a tuple-valued state variable ----

#[test]
fn a_tuple_variable_has_a_sort() {
    holds("t", "t = <<1, 2, 3>>", "t[1] = 1 /\\ t[3] = 3");
    fails("t", "t = <<1, 2, 3>>", "t[2] = 5");
}

#[test]
fn a_tuple_may_mix_component_types() {
    holds("t", "t = <<1, \"a\">>", "t[1] = 1 /\\ t[2] = \"a\"");
}

#[test]
fn domain_of_a_tuple_variable_is_its_indices() {
    holds("t", "t = <<1, 2, 3>>", "DOMAIN t = {1, 2, 3}");
}

#[test]
fn except_on_a_tuple_variable() {
    holds("t", "t = <<1, 2>>", "[t EXCEPT ![1] = 9] = <<9, 2>>");
}

// ---- sets of tuples: the shape that motivated this ----

/// `Set(<<Str, Str>>)` was the most common unsortable state type in the
/// corpus. Its members come out of the theory as datatype terms and have to
/// meet tuple literals written in the specification.
#[test]
fn a_set_of_tuples_is_a_state_variable() {
    holds("s", "s = {<<1, 2>>}", "<<1, 2>> \\in s");
    holds("s", "s = {<<1, 2>>}", "<<1, 3>> \\notin s");
}

/// `Cardinality` of a set **variable** an assertion pins to a literal set
/// is exact: the asserted equality `s = {…}` reaches the operand's
/// support-exact count through the `a = b → card(a) = card(b)` rule
/// (landed 2026-09-15, mirroring Z3's `theory_finite_set_size::
/// add_eq_axioms`). Before that rule the support recursion did not follow
/// equalities and the claim was honestly `Unknown`; the test pins the
/// improvement — and its sibling keeps the genuine decline: a variable
/// with **no** pinning equality still has unknown members.
#[test]
fn cardinality_of_a_pinned_set_variable_is_exact() {
    assert!(matches!(
        claim("s", "s = {<<1, 2>>, <<3, 4>>}", "Cardinality(s) = 2"),
        Outcome::NoViolationWithin(0)
    ));
    assert!(matches!(
        claim("s", "s = {<<1, 2>>, <<3, 4>>}", "Cardinality(s) = 3"),
        Outcome::Violation { step: 0 }
    ));
}

/// An unpinned set variable decides too: the slack encoding gives `|s| = 2`
/// over any element sort an honest `sat` (the counting equation's slack
/// absorbs the anonymous members), so nothing here declines anymore.
#[test]
fn cardinality_of_an_unpinned_set_variable_decides() {
    // The invariant does not hold of *every* state, and the violation is
    // witnessed by a real model (the slack encoding plus synthesis) — not
    // a guess.
    assert!(matches!(
        claim("s", "TRUE", "Cardinality(s) = 2"),
        Outcome::Violation { step: 0 }
    ));
    // A tautologous cardinality bound holds everywhere.
    assert!(matches!(
        claim("s", "TRUE", "Cardinality(s) >= 0"),
        Outcome::NoViolationWithin(0)
    ));
    // And a bound no family can meet is refuted, not declined.
    assert!(matches!(
        claim("s", "Cardinality(s) >= 0", "Cardinality(s) < 0"),
        Outcome::Violation { step: 0 }
    ));
}

#[test]
fn a_set_of_records() {
    holds("s", "s = {[a |-> 1]}", "[a |-> 1] \\in s");
    holds("s", "s = {[a |-> 1]}", "[a |-> 2] \\notin s");
}

/// Set operations over tuple elements go through the theory, not the arena.
#[test]
fn set_operations_over_tuples() {
    holds(
        "s",
        "s = {<<1, 2>>, <<3, 4>>}",
        "s \\ {<<1, 2>>} = {<<3, 4>>}",
    );
    holds(
        "s",
        "s = {<<1, 2>>}",
        "s \\cup {<<3, 4>>} = {<<1, 2>>, <<3, 4>>}",
    );
}

/// Quantifying over a set of tuples, with the bound variable used as a tuple.
/// The bound set is written out, because a bounded quantifier is *instantiated*
/// per candidate and a set variable has no candidate list.
#[test]
fn a_quantifier_over_a_set_of_tuples() {
    holds("x", "x = 0", "\\A p \\in {<<1, 2>>, <<1, 3>>} : p[1] = 1");
    fails("x", "x = 0", "\\A p \\in {<<1, 2>>, <<1, 3>>} : p[2] = 2");
    holds("x", "x = 0", "\\E p \\in {<<1, 2>>, <<3, 4>>} : p[2] = 4");
}

// ---- functions into records ----

/// `(Str -> [..])` — a function whose range is a record — was the other big
/// unsortable state type.
#[test]
fn a_function_into_a_record() {
    holds(
        "f",
        "f = [i \\in {1, 2} |-> [n |-> i, ok |-> TRUE]]",
        "f[1].n = 1 /\\ f[2].ok",
    );
    fails(
        "f",
        "f = [i \\in {1, 2} |-> [n |-> i, ok |-> TRUE]]",
        "f[2].n = 1",
    );
}

// ---- what is still refused ----

/// An **open** record — one where inference only ever saw field accesses, so
/// the value may carry fields this type does not list — is refused. A datatype
/// over the known fields would make two records that differ only in the rest
/// compare *equal*, which hides a counterexample rather than manufacturing
/// one.
#[test]
fn an_open_record_state_type_is_refused() {
    let src = r"
---- MODULE Open ----
EXTENDS Integers
VARIABLE r
Init == r.a = 1
Next == UNCHANGED r
Inv  == r.a = 1
====
";
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let err = Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm)
        .err()
        .expect("an open record has no sort");
    assert!(
        matches!(err, nixie_tla_check::bmc::SetupError::NoSort { .. }),
        "an open record must be refused by name, got: {err}"
    );
}
