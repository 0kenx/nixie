//! Parser regression tests for the `get-consequences` command and for
//! threading `:named` assertion annotations into a name-carrying command.
//!
//! Findings fixed:
//!   * `get-consequences` previously hit the parser's balance-skip fallback and
//!     was silently dropped; it now parses into a
//!     [`Command::GetConsequences`] carrying its two term-lists.
//!   * `(assert (! phi :named foo))` previously produced a plain
//!     `Command::Assert` that discarded the name, so script-driven
//!     `(get-unsat-core)` was always empty; the top-level `:named` annotation
//!     is now promoted to [`Command::AssertNamed`].

use nixie_core::ast::TermManager;
use nixie_core::smtlib::{Command, parse_script};

#[test]
fn get_consequences_parses_two_term_lists() {
    let mut manager = TermManager::new();
    let script = "(declare-const a Bool)(declare-const b Bool)(declare-const c Bool)\
                  (get-consequences (a) (b c))";
    let commands = parse_script(script, &mut manager).expect("should parse get-consequences");
    let (asms, vars) = commands
        .iter()
        .find_map(|c| match c {
            Command::GetConsequences(asms, vars) => Some((asms.clone(), vars.clone())),
            _ => None,
        })
        .expect("expected a GetConsequences command");
    assert_eq!(asms.len(), 1, "one assumption");
    assert_eq!(vars.len(), 2, "two queried variables");
}

#[test]
fn get_consequences_allows_empty_assumption_list() {
    let mut manager = TermManager::new();
    let script = "(declare-const a Bool)(declare-const b Bool)(get-consequences () (a b))";
    let commands = parse_script(script, &mut manager).expect("should parse get-consequences");
    let (asms, vars) = commands
        .iter()
        .find_map(|c| match c {
            Command::GetConsequences(asms, vars) => Some((asms.clone(), vars.clone())),
            _ => None,
        })
        .expect("expected a GetConsequences command");
    assert!(asms.is_empty(), "no assumptions");
    assert_eq!(vars.len(), 2, "two queried variables");
}

#[test]
fn top_level_named_annotation_becomes_assert_named() {
    let mut manager = TermManager::new();
    let script = "(declare-const p Bool)(assert (! p :named foo))";
    let commands = parse_script(script, &mut manager).expect("should parse named assert");
    assert!(
        commands
            .iter()
            .any(|c| matches!(c, Command::AssertNamed(_, name) if name == "foo")),
        "expected AssertNamed(_, \"foo\"), got {commands:?}"
    );
}

#[test]
fn plain_assertion_stays_unnamed() {
    let mut manager = TermManager::new();
    let script = "(declare-const p Bool)(assert p)";
    let commands = parse_script(script, &mut manager).expect("should parse plain assert");
    assert!(commands.iter().any(|c| matches!(c, Command::Assert(_))));
    assert!(
        !commands
            .iter()
            .any(|c| matches!(c, Command::AssertNamed(_, _)))
    );
}

#[test]
fn named_annotation_on_subterm_does_not_name_the_assertion() {
    // The `:named` sits on a *sub*-expression, not the asserted formula, so the
    // command must stay a plain `Assert` – the annotation key is the inner term
    // `a`, never the returned top-level `(=> a b)` term.
    let mut manager = TermManager::new();
    let script = "(declare-const a Bool)(declare-const b Bool)(assert (=> (! a :named x) b))";
    let commands = parse_script(script, &mut manager).expect("should parse");
    assert!(
        !commands
            .iter()
            .any(|c| matches!(c, Command::AssertNamed(_, _))),
        "a sub-term :named must not name the whole assertion; got {commands:?}"
    );
}
