//! The arena encoding of sets, checked against the evaluator.
//!
//! The evaluator is validated against TLC by `bench/tla_eval`, so agreeing
//! with it is agreement with TLA+ semantics, transitively. Each case here
//! asserts the *sound* property: a claim the evaluator says is true must
//! encode to a formula whose negation the solver refutes.

use nixie_core::TermManager;
use nixie_solver::{Solver, SolverResult};
use nixie_tla::{Evaluator, Lowerer};
use nixie_tla_check::{EncodeError, Encoder};
use nixie_tla_syntax::parse_file;

fn lower(body: &str) -> nixie_tla::KeraRef {
    let src = format!("---- MODULE M ----\nEXTENDS Integers, FiniteSets\nA == {body}\n====\n");
    let parsed = parse_file(&src).expect("parses");
    let m = parsed.module;
    let mut low = Lowerer::new();
    low.add_module(&m);
    low.lower_named(&m, "A").expect("lowers")
}

/// Encode `body`, assert the evaluator's answer about it, and check validity.
fn agrees(body: &str) {
    let k = lower(body);
    let value = Evaluator::new().eval(&k).expect("evaluates");
    let mut tm = TermManager::new();
    let encoded = Encoder::new().encode(&k, &mut tm).expect("encodes");
    let claim = match &value {
        nixie_tla::Value::Bool(true) => encoded,
        nixie_tla::Value::Bool(false) => tm.mk_not(encoded),
        nixie_tla::Value::Int(n) => {
            let lit = tm.mk_int(num_bigint::BigInt::from(*n));
            tm.mk_eq(encoded, lit)
        }
        other => panic!("`{body}` evaluates to {other}, which this helper cannot claim"),
    };
    let negated = tm.mk_not(claim);
    let mut solver = Solver::new();
    solver.assert(negated, &mut tm);
    assert_eq!(
        solver.check(&mut tm),
        SolverResult::Unsat,
        "`{body}`: evaluator says {value}, solver disagreed"
    );
}

fn encode_err(body: &str) -> EncodeError {
    let k = lower(body);
    let mut tm = TermManager::new();
    Encoder::new()
        .encode(&k, &mut tm)
        .err()
        .unwrap_or_else(|| panic!("expected `{body}` to be declined"))
}

#[test]
fn membership() {
    for b in [
        "1 \\in {1, 2, 3}",
        "4 \\in {1, 2, 3}",
        "1 \\in {}",
        "3 \\in 1..5",
        "0 \\in 1..5",
    ] {
        agrees(b);
    }
}

#[test]
fn binary_operations() {
    for b in [
        "{1, 2} \\cup {3} = {1, 2, 3}",
        "{1, 2, 3} \\cap {2, 3, 4} = {2, 3}",
        "{1, 2, 3} \\ {2} = {1, 3}",
        "{1, 2} \\cup {} = {1, 2}",
        "{1, 2} \\cap {} = {}",
    ] {
        agrees(b);
    }
}

/// Equality is extensional, which is the only definition TLA+ has. Comparing
/// candidate lists would make each of these false.
#[test]
fn equality_is_extensional_not_structural() {
    for b in [
        "{1, 1} = {1}",
        "{1, 2} = {2, 1}",
        "{1, 2} \\cup {2} = {1, 2}",
        "{x \\in 1..4 : x > 2} = {3, 4}",
    ] {
        agrees(b);
    }
}

#[test]
fn comprehensions() {
    for b in [
        "{x \\in 1..5 : x % 2 = 0} = {2, 4}",
        "{x * 2 : x \\in 1..3} = {2, 4, 6}",
        "{x \\in {} : x > 0} = {}",
    ] {
        agrees(b);
    }
}

#[test]
fn bounded_quantifiers() {
    for b in [
        "\\A x \\in 1..4 : x > 0",
        "\\A x \\in 1..4 : x > 2",
        "\\E x \\in 1..4 : x = 3",
        "\\E x \\in 1..4 : x = 9",
        "\\A x \\in {} : x > 0",
        "\\E x \\in {} : x > 0",
    ] {
        agrees(b);
    }
}

/// Nested quantifiers instantiate a copy of the body per candidate pair, so
/// this is the case where the encoding's size starts to matter.
#[test]
fn nested_quantifiers() {
    for b in [
        "\\A x \\in 1..3 : \\A y \\in 1..3 : x + y > 1",
        "\\A x \\in 1..3 : \\E y \\in 1..3 : y > x",
        "\\E x \\in 1..3 : \\A y \\in 1..3 : x <= y",
    ] {
        agrees(b);
    }
}

#[test]
fn union_of_a_set_of_sets() {
    for b in ["UNION {{1, 2}, {3}} = {1, 2, 3}", "UNION {{1}, {1}} = {1}"] {
        agrees(b);
    }
}

/// The case candidate lists get wrong if counted naively. `{1, 1}` has **two**
/// candidates denoting one value, and `{1,2} \cup {2}` has three denoting two.
#[test]
fn cardinality_does_not_count_duplicate_candidates() {
    for b in [
        "Cardinality({1, 2, 3}) = 3",
        "Cardinality({1, 1}) = 1",
        "Cardinality({1, 2} \\cup {2}) = 2",
        "Cardinality({}) = 0",
        "Cardinality({x \\in 1..6 : x % 2 = 0}) = 3",
    ] {
        agrees(b);
    }
}

#[test]
fn sets_of_sets_nest() {
    for b in [
        "{1, 2} \\in {{1, 2}, {3}}",
        "{3} \\in {{1, 2}, {3}}",
        "{1} \\in {{1, 2}, {3}}",
    ] {
        agrees(b);
    }
}

/// A set whose candidates cannot be listed is refused by that name. The
/// distinction from "unsupported" is the point: the construct is understood,
/// and what is missing is a *bound*.
#[test]
fn a_symbolic_range_has_no_candidate_list() {
    let k = lower("\\A x \\in 1..3 : x > 0");
    let mut tm = TermManager::new();
    Encoder::new()
        .encode(&k, &mut tm)
        .expect("a literal range is enumerable");

    assert!(matches!(
        encode_err("{1} \\cup 2"),
        EncodeError::NotEnumerable(_)
    ));
}

/// The candidate budget turns a blow-up into a reported refusal rather than an
/// out-of-memory kill.
#[test]
fn the_candidate_budget_is_enforced() {
    let k = lower("\\A x \\in 1..100000 : x > 0");
    let mut tm = TermManager::new();
    assert!(matches!(
        Encoder::new().encode(&k, &mut tm),
        Err(EncodeError::TooManyCandidates { .. })
    ));
}
