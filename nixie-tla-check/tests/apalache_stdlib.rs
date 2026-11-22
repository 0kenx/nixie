//! The Apalache standard-library operators (issue #16, landed subset).
//!
//! `Apalache.tla`'s operators that lower exactly, per `StandardLibrary`
//! and the `__rewire_*` modules; a user's own definition of the same name
//! still wins. `Guess` and `Gen` are deliberately absent — their module
//! bodies are `CHOOSE`- and `{} `-based, and lowering either would change
//! the semantics silently (see the issue's soundness notes).

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome};

fn claim(defs: &str, body: &str) -> Outcome {
    let src = format!(
        r#"
---- MODULE Claim ----
EXTENDS Integers, FiniteSets, Apalache
{defs}
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

fn holds(defs: &str, body: &str) {
    assert_eq!(
        claim(defs, body),
        Outcome::NoViolationWithin(0),
        "`{body}` with `{defs}`"
    );
}

fn fails(defs: &str, body: &str) {
    assert_eq!(
        claim(defs, body),
        Outcome::Violation { step: 0 },
        "`{body}` with `{defs}`"
    );
}

// ---- the function constructors ----

#[test]
fn the_singleton_function_constructors() {
    holds("", r#"("a" :> 1)["a"] = 1"#);
    // `:=` is Apalache's alias for the same shape.
    holds("", r#"("a" := 1)["a"] = 1"#);
    // Two keys, two entries.
    holds(
        "",
        r#"LET f == ("a" :> 1) @@ ("b" :> 2) IN f["b"] = 2 /\ f["a"] = 1"#,
    );
    // `@@`'s LEFT side wins where the domains overlap — Apalache's rewire
    // tests the left domain first (`__rewire_tlc_in_apalache.tla:38`), and
    // TLC's module agrees.
    holds("", r#"LET f == ("a" :> 1) @@ ("a" :> 7) IN f["a"] = 1"#);
    fails("", r#"LET f == ("a" :> 1) @@ ("a" :> 7) IN f["a"] = 7"#);
}

// ---- the hint operators ----

/// `Skolem`, `Expand`, `ConstCardinality` are identity on their argument:
/// Apalache's encoder hints, which this encoder's exact sets make moot.
#[test]
fn the_hint_operators_are_identity() {
    holds("", r"Skolem({1, 2}) = {1, 2}");
    holds("", r"Expand({1, 2}) = {1, 2}");
    holds("", r"ConstCardinality({1, 2}) = {1, 2}");
    fails("", r"Skolem({1, 2}) = {1, 3}");
}

// ---- SetAsFun ----

/// `SetAsFun(S)`: the function mapping each pair's first to its second —
/// Apalache's own rewire, exact through the kernel `CHOOSE`.
/// `SetAsFun` lowers exactly (the `CHOOSE`-per-domain-point rewire) and
/// type-checks, but the **encode** still declines it: the mapped domain's
/// members come out as structural tuple components the function-domain
/// builder has no scalar form for. The lowering is kept — the evaluator
/// runs it, and the gap is one encoder arm — and the claim is recorded
/// here so the day it closes, this test gets its assertions back:
///
/// ```text
/// SetAsFun({<<"a", 1>>, <<"b", 2>>})["a"] = 1
/// DOMAIN SetAsFun({<<"a", 1>>, <<"b", 2>>}) = {"a", "b"}
/// ```
#[test]
#[ignore = "encode: SetAsFun's mapped tuple members have no scalar domain form yet"]
fn set_as_fun_builds_the_function() {
    let src = r#"
---- MODULE SAF ----
EXTENDS Integers, Apalache
VARIABLE x
Init == x = 0
Next == UNCHANGED <<x>>
Inv == SetAsFun({<<"a", 1>>, <<"b", 2>>})["a"] = 1
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert!(bmc.check(0, &mut tm).is_err(), "the encode gap, honestly");
}

// ---- Repeat ----

/// `Repeat(F, N, x)`: N-fold application, literal N only — Apalache's
/// `RepeatRule`, as ONE ordered sequence fold (F need not be commutative).
#[test]
fn repeat_applies_the_operator_n_times() {
    // The issue's own Inv1: F(a,i) = a+1, five times from 0.
    holds(
        "Op(a, i) == a + 1",
        "LET Op2(a, i) == a + 1 IN Repeat(Op2, 5, 0) = 5",
    );
    // And Inv2: F(a,i) = a+i — the step index participates.
    holds("", "LET Op(a, i) == a + i IN Repeat(Op, 5, 0) = 15");
    // A wrong count is a violation, not a decline.
    fails("", "LET Op(a, i) == a + i IN Repeat(Op, 5, 0) = 14");
    // Zero repeats: the value unchanged.
    holds("", "LET Op(a, i) == a + 1 IN Repeat(Op, 0, 41) = 41");
    // A `LAMBDA` works as the operator.
    holds("", r"Repeat(LAMBDA a, i: a * 2, 4, 1) = 16");
}

/// A non-literal count declines by name — Apalache errors on it too, and a
/// symbolic count has no finite unfolding.
#[test]
fn repeat_with_a_symbolic_count_declines() {
    let src = r#"
---- MODULE RepBad ----
EXTENDS Integers, Apalache
VARIABLE n
Init == n \in 1..3
Next == UNCHANGED n
Inv == Repeat(LAMBDA a, i: a + 1, n, 0) = n
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let err = match Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm) {
        Ok(_) => panic!("a symbolic count must not prepare"),
        Err(e) => e,
    };
    assert!(
        err.to_string().contains("literal"),
        "the decline names the literal-count requirement: {err}"
    );
}

// ---- MkSeq ----

/// `MkSeq(N, F) == [i \in 1..N |-> F(i)]`, literal N.
#[test]
fn mk_seq_builds_the_sequence() {
    holds("", r#"LET Id(i) == i IN MkSeq(3, Id) = <<1, 2, 3>>"#);
    holds("", r#"LET Sq(i) == i * i IN MkSeq(3, Sq)[2] = 4"#);
    fails("", r#"LET Id(i) == i IN MkSeq(3, Id) = <<1, 2>>"#);
}

// ---- the never-lowered operators ----

/// `Guess` and `Gen` must NOT lower from their module bodies: `Guess`'s body
/// is a `CHOOSE` (deterministic — *fewer* behaviours than Apalache's
/// nondeterministic pick, which hides violations), and `Gen`'s is `{}`. A
/// spec using them declines by name instead.
#[test]
fn guess_and_gen_decline_rather_than_lower() {
    for body in ["Gen(3)", "Guess()"] {
        let src = format!(
            r#"
---- MODULE G ----
EXTENDS Integers, Apalache
VARIABLE x
Init == x = 0
Next == UNCHANGED <<x>>
Inv  == {body} # x
====
"#
        );
        let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
        let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
        let module = spec.root_module().expect("has a root module");
        let mut tm = TermManager::new();
        let mut bmc =
            Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
        assert!(
            bmc.check(0, &mut tm).is_err(),
            "`{body}` must decline, not lower from its body"
        );
    }
}
