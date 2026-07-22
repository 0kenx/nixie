//! Regression tests for the SMT-LIB Strings regex sublanguage (RE-THEORY-01 /
//! PARITY-QF_S-01).
//!
//! Before this wave the entire `re.*` family was unparseable: the nullary
//! constants `re.none`/`re.all`/`re.allchar` hard-errored as "unknown constant
//! or symbol", while the compound operators (`re.++`, `re.*`, `re.range`,
//! `str.to_re`, ...) silently degraded to Bool-sorted uninterpreted applies.
//!
//! These tests assert that every operator now parses into a `RegLan`-sorted
//! regex node (represented as an `Apply` carrying the canonical SMT-LIB
//! operator name, since the `SortKind`/`TermKind` enums cannot be extended
//! from this crate's regex work without breaking exhaustive matches in sibling
//! crates), and that `str.in_re` accepts them.

use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::smtlib::{Command, parse_script};
use oxiz_core::sort::SortKind;

/// Parse a full script, returning the manager plus the asserted term ids.
fn parse_asserts(script: &str) -> (TermManager, Vec<TermId>) {
    let mut manager = TermManager::new();
    let commands = parse_script(script, &mut manager).expect("script should parse");
    let asserts = commands
        .into_iter()
        .filter_map(|c| match c {
            Command::Assert(t) => Some(t),
            _ => None,
        })
        .collect();
    (manager, asserts)
}

/// Assert `term` is `(str.in_re _ re)` and return the `re` operand id.
fn in_re_operand(manager: &TermManager, term: TermId) -> TermId {
    match &manager.get(term).expect("term").kind {
        TermKind::StrInRe(_, re) => *re,
        other => panic!("expected str.in_re, got {other:?}"),
    }
}

/// The operator function-name of a regex node, plus a check that it is
/// `RegLan`-sorted (a reserved `Uninterpreted("RegLan")` built-in sort).
fn regex_op_name(manager: &TermManager, term: TermId) -> String {
    let t = manager.get(term).expect("term");
    let sort_kind = &manager.sorts.get(t.sort).expect("sort").kind;
    match sort_kind {
        SortKind::Uninterpreted(spur) => {
            assert_eq!(
                manager.resolve_str(*spur),
                "RegLan",
                "regex node must carry the reserved RegLan sort"
            );
        }
        other => panic!("regex node must be RegLan-sorted, got {other:?}"),
    }
    match &t.kind {
        TermKind::Apply { func, .. } => manager.resolve_str(*func).to_string(),
        other => panic!("expected regex Apply node, got {other:?}"),
    }
}

const HEADER: &str = "(set-logic QF_S)(declare-const s String)";

fn parse_in_re(re_src: &str) -> String {
    let script = format!("{HEADER}(assert (str.in_re s {re_src}))(check-sat)");
    let (manager, asserts) = parse_asserts(&script);
    let operand = in_re_operand(&manager, asserts[0]);
    regex_op_name(&manager, operand)
}

#[test]
fn nullary_constants_parse() {
    assert_eq!(parse_in_re("re.none"), "re.none");
    assert_eq!(parse_in_re("re.all"), "re.all");
    assert_eq!(parse_in_re("re.allchar"), "re.allchar");
}

#[test]
fn str_to_re_parses() {
    assert_eq!(parse_in_re(r#"(str.to_re "abc")"#), "str.to_re");
}

#[test]
fn concat_union_inter_parse() {
    assert_eq!(
        parse_in_re(r#"(re.++ (str.to_re "a") (str.to_re "b"))"#),
        "re.++"
    );
    assert_eq!(
        parse_in_re(r#"(re.union (str.to_re "a") (str.to_re "b"))"#),
        "re.union"
    );
    assert_eq!(
        parse_in_re(r#"(re.inter (re.* re.allchar) (str.to_re "a"))"#),
        "re.inter"
    );
}

#[test]
fn star_plus_opt_comp_parse() {
    assert_eq!(parse_in_re("(re.* re.allchar)"), "re.*");
    assert_eq!(parse_in_re(r#"(re.+ (str.to_re "a"))"#), "re.+");
    assert_eq!(parse_in_re(r#"(re.opt (str.to_re "a"))"#), "re.opt");
    assert_eq!(parse_in_re(r#"(re.comp (str.to_re "a"))"#), "re.comp");
}

#[test]
fn diff_and_range_parse() {
    assert_eq!(
        parse_in_re(r#"(re.diff (re.* re.allchar) (str.to_re "x"))"#),
        "re.diff"
    );
    assert_eq!(parse_in_re(r#"(re.range "0" "9")"#), "re.range");
}

#[test]
fn indexed_power_and_loop_parse() {
    assert_eq!(parse_in_re(r#"((_ re.^ 3) (str.to_re "ab"))"#), "re.^");
    assert_eq!(
        parse_in_re(r#"((_ re.loop 1 4) (str.to_re "z"))"#),
        "re.loop"
    );
}

#[test]
fn string_09_pattern_parses_without_error() {
    // The exact shape that previously errored with
    // "unknown constant or symbol: re.allchar".
    let script = format!(
        "{HEADER}(assert (str.in_re s (re.++ (re.* re.allchar) (re.range \"0\" \"9\"))))(check-sat)"
    );
    let mut manager = TermManager::new();
    let commands = parse_script(&script, &mut manager);
    assert!(
        commands.is_ok(),
        "string_09-style regex must parse, got {:?}",
        commands.err()
    );
}

#[test]
fn re_power_encodes_repetition_count_as_int_operand() {
    // ((_ re.^ 3) R) is encoded as Apply("re.^", [Int(3), R]); check the count.
    let script =
        format!(r#"{HEADER}(assert (str.in_re s ((_ re.^ 3) (str.to_re "ab"))))(check-sat)"#);
    let (manager, asserts) = parse_asserts(&script);
    let operand = in_re_operand(&manager, asserts[0]);
    match &manager.get(operand).expect("op").kind {
        TermKind::Apply { func, args } => {
            assert_eq!(manager.resolve_str(*func), "re.^");
            assert_eq!(args.len(), 2, "re.^ node = [count, regex]");
            match &manager.get(args[0]).expect("count").kind {
                TermKind::IntConst(n) => assert_eq!(n.to_string(), "3"),
                other => panic!("re.^ count must be Int, got {other:?}"),
            }
        }
        other => panic!("expected re.^ Apply, got {other:?}"),
    }
}

#[test]
fn regex_operators_are_not_bool_sorted() {
    // Guard against the old silent degradation to a Bool-sorted uninterpreted
    // apply: a regex node must never carry Bool sort.
    let (manager, asserts) = parse_asserts(&format!(
        "{HEADER}(assert (str.in_re s (re.* re.allchar)))(check-sat)"
    ));
    let operand = in_re_operand(&manager, asserts[0]);
    let sort = manager.get(operand).expect("op").sort;
    assert_ne!(
        sort, manager.sorts.bool_sort,
        "regex node must not be Bool-sorted (old degradation bug)"
    );
}
