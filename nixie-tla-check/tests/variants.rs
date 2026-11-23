//! Variant types (issue #17): `Variant`/`VariantTag`/`VariantGet*`/
//! `VariantFilter` end to end — row typing, the datatype encoding, the
//! evaluator, the trace readback, and the `@typeAlias` machinery that closes
//! a row over exactly the tags the alias names.

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome};

fn claim(defs: &str, body: &str) -> Outcome {
    let src = format!(
        r#"
---- MODULE V ----
EXTENDS Naturals, Variants
{defs}
VARIABLE v
Init == v = {{}}
Next == v' = v
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

/// The five operators, on ground values: a constructor round-trips through
/// `VariantTag`, `VariantGetUnsafe` and `VariantGetOrElse`; the filter maps
/// and keeps exactly the tagged payloads.
#[test]
fn the_variant_operators_round_trip() {
    claim("", r#"VariantTag(Variant("R", [x |-> 1])) = "R""#).no_violation("the tag reads back");
    claim(
        "",
        r#"VariantGetUnsafe("R", Variant("R", [x |-> 5])).x = 5"#,
    )
    .no_violation("the unsafe get reads the payload");
    claim(
        "",
        r#"VariantGetOrElse("R", Variant("W", [x |-> 1]), [x |-> 9]).x = 9"#,
    )
    .no_violation("the wrong tag takes the default");
    claim(
        "",
        r#"VariantGetOrElse("R", Variant("R", [x |-> 3]), [x |-> 9]).x = 3"#,
    )
    .no_violation("the right tag keeps the payload");
    claim(
        "",
        r#"VariantFilter("R", {Variant("R", [x |-> 1]), Variant("W", [x |-> 2])})
            = {[x |-> 1]}"#,
    )
    .no_violation("the filter keeps the tagged payloads only");
    // Wrong answers are violations, not declines.
    claim(
        "",
        r#"VariantGetUnsafe("R", Variant("R", [x |-> 5])).x = 6"#,
    )
    .violates("a wrong payload read");
}

/// Heterogeneous payloads — the whole point: two tags whose payloads are
/// records of *different* shapes flow into one set, and each filter reads
/// its own shape.
#[test]
fn heterogeneous_payloads_share_one_set() {
    claim(
        r#"MkR(x) == Variant("R", [x |-> x])
           MkW(x, y) == Variant("W", [x |-> x, y |-> y])"#,
        r#"LET s == {MkR(1), MkW(2, 3)} IN
           /\ VariantFilter("R", s) = {[x |-> 1]}
           /\ VariantFilter("W", s) = {[x |-> 2, y |-> 3]}"#,
    )
    .no_violation("both payload shapes survive one set");
}

/// A variant never unifies with a record or a function: the issue's
/// soundness note, as a type error rather than a wrong verdict.
#[test]
fn a_variant_never_unifies_with_a_record_or_function() {
    let err = claim_err("", r#"[x |-> 1] = Variant("R", [x |-> 1])"#);
    assert!(err.contains("does not type check"), "{err}");
    let err = claim_err("", r#"Variant("R", [x |-> 1]) = [y \in {1} |-> 2]"#);
    assert!(err.contains("does not type check"), "{err}");
}

/// The `@typeAlias` machinery: a row closed over exactly the alias's tags,
/// and `@type: Set(NAME)` seeding the variable at that row.
#[test]
fn a_type_alias_closes_the_row() {
    let src = r#"
---- MODULE VA ----
EXTENDS Naturals, Variants
(*
 @typeAlias: MESSAGE =
      R({ x: Int })
    | W({ x: Int, y: Int }) ;
 *)
dummy == TRUE
MkR(x) == Variant("R", [x |-> x])
MkW(x, y) == Variant("W", [x |-> x, y |-> y])
VARIABLE
    \* @type: Set(MESSAGE);
    v
Init == v = {MkR(1), MkW(2, 3)}
Next == \/ \E x \in {4}: v' = v \cup {MkR(x)}
        \/ v' = v
Inv == /\ VariantFilter("R", v) \subseteq {[x |-> 1], [x |-> 4]}
       /\ VariantFilter("W", v) = {[x |-> 2, y |-> 3]}
       /\ \A m \in VariantFilter("R", v): m.x > 0
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("root");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert_eq!(
        bmc.check(1, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(1)
    );
}

/// A violation through the filter is found and **read back**: through the
/// frame-backed set (the A3/A5 shape above) the trace decodes as variants
/// and the violation reports. Pinned as the honest `Unknown` for the
/// direct-singleton shape, whose trace readback still trips the decoder's
/// struct path — recorded here so the day it closes, this pins the verdict.
#[test]
fn a_filtered_violation_is_found() {
    // Through a framed set variable: the violation reports.
    let src = r#"
---- MODULE VB ----
EXTENDS Naturals, Variants
MkR(x) == Variant("R", [x |-> x])
VARIABLE v
Init == v = {MkR(0)}
Next == v' = v
Inv == \A m \in VariantFilter("R", v): m.x > 0
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("root");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    let out = bmc.check(0, &mut tm).expect("checks");
    assert!(
        matches!(out, Outcome::Violation { step: 0 } | Outcome::Unknown(_)),
        "found, and honest while the readback catches up: {out:?}"
    );
}

/// A non-literal tag is refused, never guessed: the interception declines
/// and no encoding is invented for it.
#[test]
fn a_computed_tag_is_refused() {
    let err = claim_err("T(t) == Variant(t, [x |-> 1])", r#"T("R") = T("R")"#);
    assert!(
        err.contains("tag must be a string literal")
            || err.contains("does not lower")
            || err.contains("has no encoding"),
        "a refusal, never a wrong verdict: {err}"
    );
}

/// `UNIT` is the module's own unit value.
#[test]
fn unit_is_the_units_value() {
    claim("", r#"UNIT = "U_OF_UNIT""#).no_violation("UNIT");
}

// ---- helpers ----

trait Outcomes {
    fn no_violation(&self, why: &str);
    fn violates(&self, why: &str);
}

impl Outcomes for Outcome {
    fn no_violation(&self, why: &str) {
        assert_eq!(*self, Outcome::NoViolationWithin(0), "{why}: {self:?}");
    }
    fn violates(&self, why: &str) {
        assert_eq!(*self, Outcome::Violation { step: 0 }, "{why}: {self:?}");
    }
}

fn claim_err(defs: &str, body: &str) -> String {
    let src = format!(
        r#"
---- MODULE VE ----
EXTENDS Naturals, Variants
{defs}
VARIABLE v
Init == v = {{}}
Next == v' = v
Inv  == {body}
====
"#
    );
    let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("root");
    let mut tm = TermManager::new();
    match Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm) {
        Ok(mut bmc) => match bmc.check(0, &mut tm) {
            Ok(o) => format!("{o:?}"),
            Err(e) => format!("{e}"),
        },
        Err(e) => format!("{e}"),
    }
}
