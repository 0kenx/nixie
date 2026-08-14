//! End-to-end theory tests for `str.in_re` membership (RE-THEORY-01 /
//! PARITY-QF_S-01).
//!
//! These exercise the full in-scope path: the core parser turns the SMT-LIB
//! regex sublanguage into `RegLan`-sorted AST nodes, [`compile_regex`] lowers a
//! ground regex operand into a Brzozowski-derivative [`Regex`], and the
//! [`StringSolver`] decides membership – including *model construction* for
//! variables constrained only by regex membership (previously returned
//! `Unknown`, matching z3's `Sat`), negated membership, empty-intersection
//! conflicts, and length interaction.
//!
//! This is exactly the translation an SMT solver's string-theory dispatch must
//! perform, so it doubles as executable documentation of that hook.

use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::smtlib::{Command, parse_script};
use oxiz_theories::string::{StringSolver, compile_regex};
use oxiz_theories::{Theory, TheoryCheckResult};

/// Translate the assertions of a QF_S script into `StringSolver` constraints
/// and run `check`, returning the outcome and any string model.
fn solve(script: &str) -> (TheoryCheckResult, Vec<(TermId, String)>) {
    let mut manager = TermManager::new();
    let commands = parse_script(script, &mut manager).expect("script should parse");
    let mut solver = StringSolver::new();

    for cmd in commands {
        let Command::Assert(assertion) = cmd else {
            continue;
        };
        translate_assertion(&manager, &mut solver, assertion, assertion);
    }

    let result = solver.check().expect("check must not error");
    let model = solver.get_assignments();
    (result, model)
}

/// Translate one boolean assertion (possibly negated) into a solver constraint.
/// `origin` is the top-level assertion term used for conflict explanations.
fn translate_assertion(
    manager: &TermManager,
    solver: &mut StringSolver,
    term: TermId,
    origin: TermId,
) {
    match &manager.get(term).expect("term").kind {
        // `(not <atom>)`: recurse with the polarity flipped for memberships.
        TermKind::Not(inner) => {
            if let TermKind::StrInRe(s, re) = &manager.get(*inner).expect("inner").kind {
                add_membership(manager, solver, *s, *re, false, origin);
            }
        }
        // `(str.in_re s R)`: positive membership.
        TermKind::StrInRe(s, re) => {
            add_membership(manager, solver, *s, *re, true, origin);
        }
        // `(= (str.len s) n)`: exact length constraint.
        TermKind::Eq(a, b) => {
            if let Some((var, len)) = length_eq(manager, solver, *a, *b) {
                solver.add_length_eq(var, len, origin);
            }
        }
        _ => {}
    }
}

fn add_membership(
    manager: &TermManager,
    solver: &mut StringSolver,
    s: TermId,
    re: TermId,
    positive: bool,
    origin: TermId,
) {
    let var = solver.get_or_create_var(s);
    if let Some(regex) = compile_regex(manager, re) {
        solver.add_regex_membership(var, regex, positive, origin);
    }
    // Non-ground regexes yield None -> no constraint added; the solver then
    // returns an honest Unknown rather than an unsound result.
}

/// Recognise `(str.len s) = n` / `n = (str.len s)` and return `(var, n)`.
fn length_eq(
    manager: &TermManager,
    solver: &mut StringSolver,
    a: TermId,
    b: TermId,
) -> Option<(u32, i64)> {
    let (len_arg, n) = match (&manager.get(a)?.kind, &manager.get(b)?.kind) {
        (TermKind::StrLen(s), TermKind::IntConst(n)) => (*s, n),
        (TermKind::IntConst(n), TermKind::StrLen(s)) => (*s, n),
        _ => return None,
    };
    let len = n.to_string().parse::<i64>().ok()?;
    Some((solver.get_or_create_var(len_arg), len))
}

const HEADER: &str = "(set-logic QF_S)(declare-const s String)(declare-const t String)";

fn assert_sat_with<F: Fn(&str) -> bool>(script: &str, pred: F) {
    let (result, model) = solve(script);
    assert!(
        matches!(result, TheoryCheckResult::Sat),
        "expected Sat, got {result:?}"
    );
    let value = model
        .iter()
        .find(|(_, _)| true)
        .map(|(_, v)| v.clone())
        .unwrap_or_default();
    assert!(
        pred(&value),
        "constructed model {value:?} does not satisfy the expected property"
    );
}

#[test]
fn digit_suffix_membership_is_sat_with_model() {
    // s ∈ .*[0-9]: satisfiable; the witness must end in a digit.
    let script = format!(
        "{HEADER}(assert (str.in_re s (re.++ (re.* re.allchar) (re.range \"0\" \"9\"))))(check-sat)"
    );
    assert_sat_with(&script, |w| {
        w.chars().last().is_some_and(|c| c.is_ascii_digit())
    });
}

#[test]
fn union_literal_membership_is_sat_with_model() {
    // s ∈ (cat|dog): the model must be exactly one of them.
    let script = format!(
        "{HEADER}(assert (str.in_re s (re.union (str.to_re \"cat\") (str.to_re \"dog\"))))(check-sat)"
    );
    assert_sat_with(&script, |w| w == "cat" || w == "dog");
}

#[test]
fn intersection_emptiness_is_unsat() {
    // s ∈ [0-9] ∧ s ∈ [a-z]: no single character is in both -> Unsat.
    let script = format!(
        "{HEADER}\
         (assert (str.in_re s (re.range \"0\" \"9\")))\
         (assert (str.in_re s (re.range \"a\" \"z\")))\
         (check-sat)"
    );
    let (result, _) = solve(&script);
    assert!(
        matches!(result, TheoryCheckResult::Unsat(_)),
        "empty intersection must be Unsat, got {result:?}"
    );
}

#[test]
fn negated_membership_is_sat_with_avoiding_model() {
    // s ∈ (a|b|c) ∧ ¬(s ∈ {"a"}): witness must be "b" or "c".
    let script = format!(
        "{HEADER}\
         (assert (str.in_re s (re.union (str.to_re \"a\") (str.to_re \"b\") (str.to_re \"c\"))))\
         (assert (not (str.in_re s (str.to_re \"a\"))))\
         (check-sat)"
    );
    assert_sat_with(&script, |w| w == "b" || w == "c");
}

#[test]
fn positive_and_negated_same_regex_is_unsat() {
    // s ∈ "x" ∧ ¬(s ∈ "x"): contradictory -> Unsat.
    let script = format!(
        "{HEADER}\
         (assert (str.in_re s (str.to_re \"x\")))\
         (assert (not (str.in_re s (str.to_re \"x\"))))\
         (check-sat)"
    );
    let (result, _) = solve(&script);
    assert!(
        matches!(result, TheoryCheckResult::Unsat(_)),
        "positive+negated same membership must be Unsat, got {result:?}"
    );
}

#[test]
fn membership_with_length_is_sat_with_model() {
    // s ∈ a* ∧ len(s) = 3 -> "aaa".
    let script = format!(
        "{HEADER}\
         (assert (str.in_re s (re.* (str.to_re \"a\"))))\
         (assert (= (str.len s) 3))\
         (check-sat)"
    );
    assert_sat_with(&script, |w| w == "aaa");
}

#[test]
fn power_and_loop_memberships_are_sat() {
    let pow = format!("{HEADER}(assert (str.in_re s ((_ re.^ 2) (str.to_re \"ab\"))))(check-sat)");
    assert_sat_with(&pow, |w| w == "abab");

    let lp =
        format!("{HEADER}(assert (str.in_re s ((_ re.loop 2 3) (str.to_re \"z\"))))(check-sat)");
    assert_sat_with(&lp, |w| w == "zz" || w == "zzz");
}

#[test]
fn complement_membership_is_sat() {
    // s ∈ comp("no"): the empty string is a valid witness (≠ "no").
    let script = format!("{HEADER}(assert (str.in_re s (re.comp (str.to_re \"no\"))))(check-sat)");
    let (result, _) = solve(&script);
    assert!(matches!(result, TheoryCheckResult::Sat), "got {result:?}");
}
