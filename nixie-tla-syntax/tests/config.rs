//! TLC configuration files.
//!
//! The grammar is TLC's, published as EBNF by Apalache
//! (`docs/src/apalache/tlc-config.md`) and implemented in
//! `TlcConfigLexer.scala` / `TlcConfigParserApalache.scala`. These pin the
//! productions, the two extensions the published EBNF omits and real files
//! use, and — most importantly — the places where a wrong answer is quieter
//! than a rejection.

use nixie_tla_syntax::{BehaviorSpec, ConfigErrorKind, ConfigValue as V, parse_config};

fn cfg(src: &str) -> nixie_tla_syntax::TlcConfig {
    parse_config(src).expect("parses")
}

fn err(src: &str) -> ConfigErrorKind {
    parse_config(src).expect_err("should not parse").kind
}

// ---- constants ----

#[test]
fn an_integer_assignment() {
    let c = cfg("CONSTANT N = 3");
    assert_eq!(c.assignments.get("N"), Some(&V::Int("3".into())));
}

/// Kept as written, never through `i64`: a `.cfg` may pin a constant to a
/// value wider than a machine integer and it has to survive exactly.
#[test]
fn a_wide_integer_survives() {
    let big = "123456789012345678901234567890";
    let c = cfg(&format!("CONSTANT N = {big}"));
    assert_eq!(c.assignments.get("N"), Some(&V::Int(big.into())));
}

#[test]
fn a_negative_integer_is_one_token() {
    let c = cfg("CONSTANT N = -7");
    assert_eq!(c.assignments.get("N"), Some(&V::Int("-7".into())));
}

/// A bare identifier on the right of `=` is a **model value** — an
/// uninterpreted constant distinct from every other value. `NoVal = NoVal` is
/// not circular, and reading it as a reference to the left-hand name would be.
#[test]
fn a_bare_identifier_is_a_model_value() {
    let c = cfg("CONSTANT NoVal = NoVal");
    assert_eq!(
        c.assignments.get("NoVal"),
        Some(&V::ModelValue("NoVal".into()))
    );
}

#[test]
fn sets_of_model_values() {
    let c = cfg("CONSTANTS Proc = {p1, p2, p3}");
    assert_eq!(
        c.assignments.get("Proc"),
        Some(&V::Set(vec![
            V::ModelValue("p1".into()),
            V::ModelValue("p2".into()),
            V::ModelValue("p3".into()),
        ]))
    );
}

#[test]
fn the_empty_set_is_a_value() {
    let c = cfg("CONSTANT S = {}");
    assert_eq!(c.assignments.get("S"), Some(&V::Set(vec![])));
}

#[test]
fn nested_sets() {
    let c = cfg("CONSTANT S = {{a}, {}}");
    assert_eq!(
        c.assignments.get("S"),
        Some(&V::Set(vec![
            V::Set(vec![V::ModelValue("a".into())]),
            V::Set(vec![]),
        ]))
    );
}

#[test]
fn booleans_and_strings() {
    let c = cfg(r#"CONSTANTS B = TRUE  C = FALSE  S = "hello world""#);
    assert_eq!(c.assignments.get("B"), Some(&V::Bool(true)));
    assert_eq!(c.assignments.get("C"), Some(&V::Bool(false)));
    assert_eq!(c.assignments.get("S"), Some(&V::Str("hello world".into())));
}

#[test]
fn a_replacement_names_a_definition() {
    let c = cfg("CONSTANT Keys <- MCKeys");
    let r = c.replacements.get("Keys").expect("has a replacement");
    assert_eq!(r.to, "MCKeys");
    assert_eq!(r.module, None);
}

#[test]
fn constants_and_replacements_mix_in_one_section() {
    let c = cfg("CONSTANTS\n N = 3\n Keys <- MCKeys\n P = {p1}\n");
    assert_eq!(c.assignments.len(), 2);
    assert_eq!(c.replacements.len(), 1);
}

/// `CONSTANTS` with nothing after it is legal and says nothing.
#[test]
fn an_empty_constant_section() {
    let c = cfg("CONSTANTS\nINVARIANT Inv");
    assert!(c.assignments.is_empty());
    assert_eq!(c.invariants, ["Inv"]);
}

// ---- the two extensions the published EBNF omits ----

/// `MCPaxos.cfg` writes `Ballot <-[Voting] MCBallot`: replace `Ballot` inside
/// the `Voting` instance. Apalache's parser rejects this; TLC accepts it.
#[test]
fn a_module_qualified_replacement() {
    for src in [
        "CONSTANT Ballot <-[Voting] MCBallot",
        "CONSTANT Ballot <- [Voting]MCBallot",
    ] {
        let c = cfg(src);
        let r = c.replacements.get("Ballot").expect("has a replacement");
        assert_eq!(r.to, "MCBallot");
        assert_eq!(r.module.as_deref(), Some("Voting"));
        assert_eq!(
            c.module_qualified_replacements(),
            [("Ballot", "Voting", "MCBallot")]
        );
    }
}

/// Kept distinct from an unqualified replacement, because the two mean
/// different things and applying one for the other checks a different
/// specification.
#[test]
fn a_qualified_replacement_is_not_an_unqualified_one() {
    let plain = cfg("CONSTANT B <- X");
    let qualified = cfg("CONSTANT B <- [M]X");
    assert!(plain.module_qualified_replacements().is_empty());
    assert_eq!(qualified.module_qualified_replacements().len(), 1);
}

/// `\o <- MCCat`, `++ <- PlusPlus`, `Plus <- +`: an operator may stand on
/// either side. The published EBNF admits only `[a-zA-Z_][a-zA-Z0-9_]*`.
#[test]
fn operators_may_be_names() {
    let c = cfg("CONSTANTS\n \\o <- MCCat\n ++ <- PlusPlus\n Plus <- +\n");
    assert_eq!(
        c.replacements.get("\\o").map(|r| r.to.as_str()),
        Some("MCCat")
    );
    assert_eq!(
        c.replacements.get("++").map(|r| r.to.as_str()),
        Some("PlusPlus")
    );
    assert_eq!(c.replacements.get("Plus").map(|r| r.to.as_str()), Some("+"));
}

/// Validated against this crate's own operator table, so punctuation that is
/// not a TLA+ operator is still an error rather than a name.
#[test]
fn punctuation_that_is_not_an_operator_is_refused() {
    assert_eq!(
        err("CONSTANT @@@@@ <- X"),
        ConfigErrorKind::NotAnOperator("@@@@@".into())
    );
}

/// `MCNanoSmall.cfg` writes `NoHash = [Nano]NoHashVal`. Recorded as written
/// and *not* interpreted: there is no specification for it to follow, and
/// guessing between the two available readings would silently check something
/// other than what the author configured.
#[test]
fn a_module_qualified_assignment_is_recorded_uninterpreted() {
    let c = cfg("CONSTANT NoHash = [Nano]NoHashVal");
    assert_eq!(
        c.assignments.get("NoHash"),
        Some(&V::ModuleQualified {
            module: "Nano".into(),
            name: "NoHashVal".into()
        })
    );
    assert_eq!(
        c.module_qualified_assignments(),
        [("NoHash", "Nano", "NoHashVal")]
    );
}

// ---- behaviour ----

#[test]
fn init_and_next() {
    assert_eq!(
        cfg("INIT Init\nNEXT Next").behavior,
        BehaviorSpec::InitNext {
            init: "Init".into(),
            next: "Next".into()
        }
    );
}

/// The grammar lists them as independent options, so either order is legal.
#[test]
fn next_before_init() {
    assert_eq!(
        cfg("NEXT Step\nINIT Start").behavior,
        BehaviorSpec::InitNext {
            init: "Start".into(),
            next: "Step".into()
        }
    );
}

#[test]
fn a_temporal_specification() {
    assert_eq!(
        cfg("SPECIFICATION Spec").behavior,
        BehaviorSpec::Temporal("Spec".into())
    );
}

/// A file with neither is legal; it simply does not say how the system moves.
#[test]
fn no_behaviour_specification_at_all() {
    assert_eq!(cfg("INVARIANT Inv").behavior, BehaviorSpec::Unspecified);
}

/// `INIT`/`NEXT` and `SPECIFICATION` both say how the system moves, and a file
/// giving both does not say which to believe. Reported rather than resolved by
/// a precedence rule nobody wrote down — picking one silently would check a
/// different specification than the author configured.
#[test]
fn two_behaviour_specifications_are_refused() {
    assert!(matches!(
        err("INIT I\nNEXT N\nSPECIFICATION Spec"),
        ConfigErrorKind::TwoBehaviourSpecs { .. }
    ));
}

/// Half a pair is incomplete, and guessing the other half from a naming
/// convention would hide that.
#[test]
fn init_without_next_is_refused() {
    assert!(matches!(
        err("INIT Init"),
        ConfigErrorKind::Unexpected { .. }
    ));
    assert!(matches!(
        err("NEXT Next"),
        ConfigErrorKind::Unexpected { .. }
    ));
}

// ---- lists, comments, layout ----

#[test]
fn singular_and_plural_keywords_are_one_production() {
    assert_eq!(cfg("INVARIANT A B").invariants, ["A", "B"]);
    assert_eq!(cfg("INVARIANTS A B").invariants, ["A", "B"]);
    assert_eq!(cfg("PROPERTY P").properties, ["P"]);
    assert_eq!(cfg("PROPERTIES P Q").properties, ["P", "Q"]);
    assert_eq!(cfg("CONSTRAINT C").state_constraints, ["C"]);
    assert_eq!(cfg("CONSTRAINTS C D").state_constraints, ["C", "D"]);
    assert_eq!(cfg("ACTION_CONSTRAINT A").action_constraints, ["A"]);
    assert_eq!(cfg("ACTION_CONSTRAINTS A B").action_constraints, ["A", "B"]);
}

/// A list ends where the next option begins — there is no separator.
#[test]
fn a_list_stops_at_the_next_keyword() {
    let c = cfg("INVARIANT TypeOK Correctness\nPROPERTY Liveness\nSPECIFICATION Spec");
    assert_eq!(c.invariants, ["TypeOK", "Correctness"]);
    assert_eq!(c.properties, ["Liveness"]);
}

/// Repeated sections accumulate, which is how multi-section files read.
#[test]
fn repeated_sections_accumulate() {
    let c = cfg("INVARIANT A\nINVARIANT B\nCONSTANT x = 1\nCONSTANT y = 2");
    assert_eq!(c.invariants, ["A", "B"]);
    assert_eq!(c.assignments.len(), 2);
}

#[test]
fn comments_are_dropped() {
    let c = cfg("\\* a line comment\nCONSTANT N = 3 \\* trailing\n(* a\n block *)\nINVARIANT Inv");
    assert_eq!(c.assignments.get("N"), Some(&V::Int("3".into())));
    assert_eq!(c.invariants, ["Inv"]);
}

/// Unlike TLA+ proper, `.cfg` layout carries no meaning: an option's arguments
/// may be on any line.
#[test]
fn layout_is_not_significant() {
    let c = cfg("CONSTANTS\n\n  N\n  =\n  3\n\nINVARIANT\n  Inv\n");
    assert_eq!(c.assignments.get("N"), Some(&V::Int("3".into())));
    assert_eq!(c.invariants, ["Inv"]);
}

#[test]
fn check_deadlock() {
    assert_eq!(cfg("CHECK_DEADLOCK FALSE").check_deadlock, Some(false));
    assert_eq!(cfg("CHECK_DEADLOCK TRUE").check_deadlock, Some(true));
    assert_eq!(cfg("INVARIANT I").check_deadlock, None);
    assert!(matches!(
        err("CHECK_DEADLOCK TRUE\nCHECK_DEADLOCK FALSE"),
        ConfigErrorKind::ConflictingCheckDeadlock
    ));
}

// ---- read but not acted on ----

/// Recognised and recorded, never silently skipped: a caller deciding whether
/// to trust a verdict needs to know what of the author's configuration was
/// read and then set aside.
#[test]
fn ignored_options_are_recorded_rather_than_skipped() {
    let c = cfg("SYMMETRY Sym\nVIEW V\nALIAS A\nPOSTCONDITION P");
    assert_eq!(c.symmetry.as_deref(), Some("Sym"));
    assert_eq!(c.view.as_deref(), Some("V"));
    assert_eq!(c.alias.as_deref(), Some("A"));
    assert_eq!(c.postcondition.as_deref(), Some("P"));
    assert_eq!(
        c.unused_options(),
        ["SYMMETRY", "VIEW", "ALIAS", "POSTCONDITION"]
    );
}

#[test]
fn a_file_with_nothing_to_ignore_reports_nothing() {
    assert!(cfg("INVARIANT Inv").unused_options().is_empty());
}

// ---- diagnostics ----

#[test]
fn an_error_carries_a_position() {
    let e = parse_config("INVARIANT Inv\nCONSTANT N = ").expect_err("incomplete");
    assert_eq!(e.span.start.line, 2);
}

#[test]
fn a_stray_token_is_not_silently_skipped() {
    assert!(matches!(
        err("NOT_A_KEYWORD x"),
        ConfigErrorKind::Unexpected { .. }
    ));
}

#[test]
fn an_unterminated_string_is_named() {
    assert_eq!(
        err("CONSTANT S = \"abc"),
        ConfigErrorKind::UnterminatedString
    );
}

#[test]
fn an_unterminated_block_comment_is_named() {
    assert_eq!(err("(* forever"), ConfigErrorKind::UnterminatedComment);
}

/// An empty file parses to an empty configuration: it constrains nothing,
/// which is different from failing to read it.
#[test]
fn an_empty_file_is_an_empty_config() {
    let c = cfg("");
    assert_eq!(c, nixie_tla_syntax::TlcConfig::default());
}
