//! `ApaFoldSet` and `ApaFoldSeqLeft`.
//!
//! These are the only standard operators whose argument is an *operator*, and
//! the kernel is deliberately first-order. Rather than grow a lambda and an
//! operator type, a fold is its own binder: lowering keeps the operator's body
//! with its two parameters free and `Kera::Fold` names them, exactly the shape
//! `\A x \in S : …` already has. Apalache does the same thing in substance —
//! its rewriter receives the operator wrapped in a `LetInEx` and inlines it
//! once per element.
//!
//! The hard part is not the fold, it is the arena. A candidate list
//! over-approximates in two independent ways: a candidate may not be in the
//! set, and two candidates may denote the same value. A step therefore only
//! takes effect when the candidate is present **and** is not a duplicate of an
//! earlier present one — the same guard `Cardinality` uses, and the same one
//! Apalache builds in `SetOps.dedup`. The tests below pin both halves,
//! because either one missing is a wrong answer rather than a missing feature.

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome};

fn spec(vars: &str, defs: &str, init: &str, body: &str) -> String {
    format!(
        r"
---- MODULE Claim ----
EXTENDS Integers, FiniteSets
VARIABLE {vars}
{defs}
Init == {init}
Next == UNCHANGED <<{vars}>>
Inv  == {body}
====
"
    )
}

fn claim(vars: &str, defs: &str, init: &str, body: &str) -> Outcome {
    let src = spec(vars, defs, init, body);
    let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
    let loaded = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = loaded.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&loaded, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    bmc.check(0, &mut tm).expect("checks")
}

fn holds(vars: &str, defs: &str, init: &str, body: &str) {
    assert_eq!(
        claim(vars, defs, init, body),
        Outcome::NoViolationWithin(0),
        "`{body}`"
    );
}

fn fails(vars: &str, defs: &str, init: &str, body: &str) {
    assert_eq!(
        claim(vars, defs, init, body),
        Outcome::Violation { step: 0 },
        "`{body}`"
    );
}

const ADD: &str = "Add(a, b) == a + b";
const SUB: &str = "Sub(a, b) == a - b";
const COUNT: &str = "Count(a, b) == a + 1";

// ---- a fold over a literal set ----

#[test]
fn fold_set_sums_a_literal() {
    holds("x", ADD, "x = 0", "ApaFoldSet(Add, 0, {1, 2, 3, 4}) = 10");
}

#[test]
fn a_wrong_sum_is_a_violation() {
    fails("x", ADD, "x = 0", "ApaFoldSet(Add, 0, {1, 2, 3, 4}) = 11");
}

#[test]
fn fold_set_over_the_empty_set_is_the_base() {
    holds("x", ADD, "x = 0", "ApaFoldSet(Add, 7, {}) = 7");
}

#[test]
fn fold_set_takes_a_lambda() {
    holds(
        "x",
        "",
        "x = 0",
        "ApaFoldSet(LAMBDA a, b: a + b, 100, {1, 2}) = 103",
    );
}

#[test]
fn fold_set_takes_a_let_bound_operator() {
    holds(
        "x",
        "",
        "x = 0",
        "LET Sum(S) == LET A(i, j) == i + j IN ApaFoldSet(A, 0, S) IN Sum({1, 2, 3}) = 6",
    );
}

// ---- the arena's two over-approximations ----

/// A candidate that is not in the set must not be folded. A difference keeps
/// every candidate of its left side and guards it, so `{1, 2, 3, 4} \ {3, 4}`
/// has four candidates and two members.
#[test]
fn an_absent_candidate_is_not_folded() {
    holds(
        "x",
        ADD,
        "x = 0",
        "ApaFoldSet(Add, 0, {1, 2, 3, 4} \\ {3, 4}) = 3",
    );
}

/// And the guard is symbolic, not decided at encode time: which candidate is
/// absent here depends on what the solver picks for `x`.
#[test]
fn an_absent_candidate_is_decided_by_the_solver() {
    holds(
        "x",
        ADD,
        "x \\in {1, 2}",
        "ApaFoldSet(Add, 0, {1, 2} \\ {x}) \\in {1, 2}",
    );
    fails(
        "x",
        ADD,
        "x \\in {1, 2}",
        "ApaFoldSet(Add, 0, {1, 2} \\ {x}) = 2",
    );
}

/// Two candidates that denote the same value are **one** member. `{x, 1}` with
/// `x = 1` is the singleton `{1}`, so counting its members gives one. Without
/// the duplicate guard this answers two, which is a wrong answer and not a
/// missing feature — it is the reason `SetOps.dedup` exists in Apalache.
#[test]
fn a_duplicate_candidate_is_folded_once() {
    holds("x", COUNT, "x = 1", "ApaFoldSet(Count, 0, {x, 1}) = 1");
}

/// And when the two candidates are genuinely different, both count.
#[test]
fn distinct_candidates_are_both_folded() {
    holds("x", COUNT, "x = 2", "ApaFoldSet(Count, 0, {x, 1}) = 2");
}

/// The guard has to be symbolic, not decided at encode time: here the solver
/// chooses `x`, and the count depends on which value it picks.
#[test]
fn the_duplicate_guard_follows_the_solver() {
    // `x \in {1, 2}` is not pinned, so a claim that holds only for `x = 2`
    // must be reported as a violation.
    fails(
        "x",
        COUNT,
        "x \\in {1, 2}",
        "ApaFoldSet(Count, 0, {x, 1}) = 2",
    );
    // Whereas the claim that covers both readings holds.
    holds(
        "x",
        COUNT,
        "x \\in {1, 2}",
        "ApaFoldSet(Count, 0, {x, 1}) \\in {1, 2}",
    );
}

/// Folding a set is the same as its cardinality when the operator counts —
/// the two share the dedup guard, and disagreeing would mean one of them is
/// wrong.
#[test]
fn counting_a_fold_agrees_with_cardinality() {
    holds(
        "x",
        COUNT,
        "x \\in {1, 2, 3}",
        "ApaFoldSet(Count, 0, {x, 1, 2}) = Cardinality({x, 1, 2})",
    );
}

// ---- sequences ----

/// Subtraction is not commutative, so this pins the direction:
/// `((100 - 1) - 2) - 3`.
#[test]
fn fold_seq_left_is_left_to_right() {
    holds(
        "x",
        SUB,
        "x = 0",
        "ApaFoldSeqLeft(Sub, 100, <<1, 2, 3>>) = 94",
    );
}

#[test]
fn fold_seq_left_over_the_empty_sequence_is_the_base() {
    holds("x", SUB, "x = 0", "ApaFoldSeqLeft(Sub, 5, <<>>) = 5");
}

/// Unlike a set, a sequence keeps its repeats.
#[test]
fn fold_seq_left_counts_repeats() {
    holds(
        "x",
        COUNT,
        "x = 0",
        "ApaFoldSeqLeft(Count, 0, <<1, 1, 1>>) = 3",
    );
}

// ---- an accumulator that is not a scalar ----

/// Apalache's own `FoldSetFun` regression: the accumulator is a *function*,
/// which is why the conditional step had to be pushed inside the value rather
/// than left to `mk_ite`.
#[test]
fn the_accumulator_may_be_a_function() {
    holds(
        "x",
        "A(p, q) == [p EXCEPT ![q] = 1]\nf == [v \\in {\"a\", \"b\"} |-> 0]",
        "x = 0",
        "ApaFoldSet(A, f, DOMAIN f) = [v \\in DOMAIN f |-> 1]",
    );
}

/// The same for a sequence, which is Apalache's `FoldSeqFun`.
#[test]
fn the_accumulator_may_be_a_function_over_a_sequence() {
    holds(
        "x",
        "A(p, q) == [p EXCEPT ![q] = 1]\nf == [v \\in {\"a\", \"b\"} |-> 0]",
        "x = 0",
        "ApaFoldSeqLeft(A, f, <<\"b\", \"a\">>) = [v \\in DOMAIN f |-> 1]",
    );
}

// ---- state ----

/// A fold over a state variable's value, which is the case Apalache's
/// `FoldSetInInit` regression covers.
#[test]
fn a_fold_reads_the_state() {
    holds("x", ADD, "x \\in {1, 2}", "ApaFoldSet(Add, 0, {x, 3}) > 3");
}
