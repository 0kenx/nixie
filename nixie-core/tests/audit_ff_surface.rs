//! Phase-0 tests for the finite-field surface language (`QF_FF`):
//! sorts, literals, operators, printing round-trips, and the honest
//! refusals (composite modulus, malformed literals, arity/type errors).
//!
//! Design reference: `docs/FF_THEORY_DESIGN.md` §2–3; surface syntax
//! mirrors cvc5's `smt2_term_parser.cpp` exactly.

use nixie_core::ast::{TermKind, TermManager};
use nixie_core::smtlib::{Command, Printer, parse_script};

/// Parse one script and return its commands; panics on parse error.
fn commands(script: &str, manager: &mut TermManager) -> Vec<Command> {
    parse_script(script, manager).unwrap_or_else(|e| panic!("parse failed: {e}"))
}

/// The single `Assert` term of a script.
fn asserted(script: &str, manager: &mut TermManager) -> nixie_core::ast::TermId {
    let cmds = commands(script, manager);
    let mut term = None;
    for cmd in cmds {
        if let Command::Assert(t) = cmd {
            term = Some(t);
        }
    }
    term.expect("script must contain an assert")
}

fn ff7(manager: &mut TermManager) -> nixie_core::sort::field::FieldId {
    let sort = manager.sorts.finite_field(7u32.into()).expect("7 is prime");
    match manager.sorts.get(sort).map(|s| s.kind.clone()) {
        Some(nixie_core::sort::SortKind::FiniteField(id)) => id,
        other => panic!("expected FiniteField sort, got {other:?}"),
    }
}

#[test]
fn finite_field_sort_parses_and_interns() {
    let mut manager = TermManager::new();
    let script = "(declare-const x (_ FiniteField 7)) (assert (= x x)) (check-sat)";
    let cmds = commands(script, &mut manager);
    assert_eq!(cmds.len(), 3);
    match &cmds[0] {
        // `DeclareConst` carries the sort as the parser-rendered text.
        Command::DeclareConst(name, sort) => {
            assert_eq!(name, "x");
            assert_eq!(sort, "(_ FiniteField 7)");
        }
        other => panic!("expected DeclareConst, got {other:?}"),
    }
}

#[test]
fn finite_field_sort_is_hash_consed_by_order() {
    let mut manager = TermManager::new();
    let a = manager
        .sorts
        .finite_field(97u32.into())
        .expect("97 is prime");
    let b = manager.sorts.finite_field(97u32.into()).expect("again");
    assert_eq!(a, b, "the same order must intern once");
}

#[test]
fn bignum_modulus_sort_parses() {
    // BN254 scalar field modulus, 254 bits: does not fit u32, u64, or the
    // u32-typed indexed-identifier path.
    let mut manager = TermManager::new();
    let script = "(declare-const x (_ FiniteField 21888242871839275222246405745257275088548364400416034343698204186575808495617)) (check-sat)";
    let cmds = commands(script, &mut manager);
    assert_eq!(cmds.len(), 2);
    match &cmds[0] {
        Command::DeclareConst(_, sort) => {
            assert_eq!(
                sort,
                "(_ FiniteField 21888242871839275222246405745257275088548364400416034343698204186575808495617)"
            );
        }
        other => panic!("expected DeclareConst, got {other:?}"),
    }
}

#[test]
fn composite_modulus_is_rejected_honestly() {
    let mut manager = TermManager::new();
    for order in ["0", "1", "4", "6", "9", "100", "1000000"] {
        let script = format!("(declare-const x (_ FiniteField {order})) (check-sat)");
        let err = parse_script(&script, &mut manager)
            .err()
            .unwrap_or_else(|| panic!("composite order {order} must be rejected"));
        let msg = err.to_string();
        assert!(
            msg.contains("not supported") || msg.contains("must be an integer"),
            "error must name the problem: {msg}"
        );
    }
}

#[test]
fn ff_literals_parse_and_normalize() {
    let mut manager = TermManager::new();
    let script = "(assert (= #f5m7 #f12m7)) (check-sat)";
    let term = asserted(script, &mut manager);
    // #f12m7 normalizes to #f5m7, so the equality is x = x and folds true.
    assert_eq!(term, manager.true_id, "12 mod 7 = 5: the literals are one");
}

#[test]
fn ff_literal_negative_ascription_form() {
    let mut manager = TermManager::new();
    let script = "(assert (= (as ff5 (_ FiniteField 7)) #f5m7)) (check-sat)";
    let term = asserted(script, &mut manager);
    assert_eq!(term, manager.true_id);
}

#[test]
fn ff_const_values_are_in_range() {
    let mut manager = TermManager::new();
    let script = "(declare-const x (_ FiniteField 7)) (assert (= x #f100m7))";
    let term = asserted(script, &mut manager);
    // The literal is 100 mod 7 = 2.
    match manager.get(term).map(|t| t.kind.clone()) {
        Some(TermKind::Eq(a, b)) => {
            let kinds: Vec<TermKind> = [a, b]
                .into_iter()
                .filter_map(|t| manager.get(t).map(|x| x.kind.clone()))
                .collect();
            let mut saw_two = false;
            for kind in kinds {
                if let TermKind::FfConst { value, field } = kind {
                    assert_eq!(field, ff7(&mut manager));
                    if value == 2i32.into() {
                        saw_two = true;
                    }
                }
            }
            assert!(saw_two, "100 mod 7 = 2 must appear");
        }
        other => panic!("expected Eq, got {other:?}"),
    }
}

#[test]
fn ff_add_parses_and_folds() {
    let mut manager = TermManager::new();
    let script = "(assert (= (ff.add #f2m7 #f3m7) #f5m7)) (check-sat)";
    let term = asserted(script, &mut manager);
    assert_eq!(term, manager.true_id, "2+3 = 5 in F_7");
}

#[test]
fn ff_mul_parses_and_folds() {
    let mut manager = TermManager::new();
    let script = "(assert (= (ff.mul #f3m7 #f5m7) #f1m7)) (check-sat)";
    let term = asserted(script, &mut manager);
    assert_eq!(term, manager.true_id, "3*5 = 15 = 1 in F_7");
}

#[test]
fn ff_neg_normalizes_to_mul_by_minus_one() {
    let mut manager = TermManager::new();
    let script = "(assert (= (ff.neg #f2m7) #f5m7)) (check-sat)";
    let term = asserted(script, &mut manager);
    assert_eq!(term, manager.true_id, "-2 = 5 in F_7");
}

#[test]
fn ff_bitsum_parses_and_folds() {
    let mut manager = TermManager::new();
    let script = "(assert (= (ff.bitsum #f1m7 #f1m7 #f0m7) #f3m7)) (check-sat)";
    let term = asserted(script, &mut manager);
    assert_eq!(term, manager.true_id, "1 + 2 + 0 = 3");
}

#[test]
fn ff_terms_print_round_trip() {
    let mut manager = TermManager::new();
    let script =
        "(declare-const x (_ FiniteField 7)) (assert (= (ff.mul x #f3m7) (ff.add x #f1m7)))";
    let term = asserted(script, &mut manager);
    let printer = Printer::new(&manager);
    let text = printer.print_term(term);
    // The printed form re-parses (inside the declaration context it needs)
    // to the same term: printing and parsing must agree on the language.
    let script = format!("(declare-const x (_ FiniteField 7)) (assert {text})");
    let re = asserted(&script, &mut manager);
    assert_eq!(re, term, "printed term must round-trip: {text}");
}

#[test]
fn ff_normal_form_sorts_children() {
    // (ff.add #f1m7 x #f2m7) folds to (ff.add #f3m7 x) with the constant
    // first; two syntactically different inputs give one interned term.
    let mut manager = TermManager::new();
    // One script: `x` is declared once and both spellings appear as
    // separate assertions.
    let cmds = commands(
        "(declare-const x (_ FiniteField 7)) \
         (assert (= (ff.add #f1m7 x #f2m7) x)) \
         (assert (= (ff.add #f2m7 #f1m7 x) x))",
        &mut manager,
    );
    let mut asserts = cmds.into_iter().filter_map(|c| match c {
        Command::Assert(t) => Some(t),
        _ => None,
    });
    let a = asserts.next().expect("first assert");
    let b = asserts.next().expect("second assert");
    assert_eq!(a, b, "constant folding + child ordering is canonical");
}

#[test]
fn ff_mixed_fields_is_a_type_error() {
    let mut manager = TermManager::new();
    let script = "(assert (= (ff.add #f1m7 #f1m5) #f2m7))";
    let err = parse_script(script, &mut manager)
        .expect_err("mixing F_7 and F_5 operands must be rejected");
    assert!(
        err.to_string().contains("different fields"),
        "error must name the type error: {err}"
    );
}

#[test]
fn ff_arity_errors_are_honest() {
    let mut manager = TermManager::new();
    for op in ["ff.add", "ff.mul", "ff.bitsum"] {
        let script = format!("(assert (= ({op} #f1m7) #f1m7))");
        let err = parse_script(&script, &mut manager)
            .err()
            .unwrap_or_else(|| panic!("{op} needs >= 2 operands"));
        assert!(err.to_string().contains("at least 2"), "{op}: {err}");
    }
}

#[test]
fn ff_reserved_prefix_is_not_a_free_function() {
    // A typo'd ff.* operator must not silently become an unconstrained
    // uninterpreted function (the class of bug `is_reserved_theory_symbol`
    // exists to prevent).
    let mut manager = TermManager::new();
    let script = "(declare-const x (_ FiniteField 7)) (assert (= (ff.sub x #f1m7) #f2m7))";
    let err = parse_script(script, &mut manager).expect_err("ff.sub does not exist");
    let msg = err.to_string();
    assert!(
        msg.contains("ff.sub") || msg.contains("not") || msg.contains("unknown"),
        "must name the unknown operator: {msg}"
    );
}

#[test]
fn malformed_ff_literals_error_at_lex_level() {
    for bad in ["#fm7", "#f5m", "#f5"] {
        let mut manager = TermManager::new();
        let script = format!("(assert (= {bad} {bad}))");
        let result = parse_script(&script, &mut manager);
        // Either a lex error surfaces through `Lexer::errors` (checked by
        // the command layer) or parsing fails; either way the literal must
        // not intern as a field constant.
        if let Ok(cmds) = result {
            let saw_ff = cmds.iter().any(|c| match c {
                Command::Assert(t) => term_has_ff_const(*t, &manager),
                _ => false,
            });
            assert!(
                !saw_ff,
                "malformed literal {bad} must not become a field constant"
            );
        }
    }
}

/// Whether any reachable term is an `FfConst` (explicit stack, DAG-aware).
fn term_has_ff_const(root: nixie_core::ast::TermId, manager: &TermManager) -> bool {
    use nixie_core::ast::get_children;
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![root];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let Some(term) = manager.get(t) {
            if matches!(term.kind, TermKind::FfConst { .. }) {
                return true;
            }
            stack.extend(get_children(&term.kind));
        }
    }
    false
}
