//! `ApaFoldSet` and `ApaFoldSeqLeft`.
//!
//! These are the only standard operators whose argument is an *operator*, and
//! the kernel is deliberately first-order. Rather than grow a lambda and an
//! operator type, a fold is its own binder: lowering keeps the operator's body
//! with its two parameters free and `Kera::Fold` names them, exactly the shape
//! `\A x \in S : …` already has. Apalache does the same thing in substance –
//! its rewriter receives the operator wrapped in a `LetInEx` and inlines it
//! once per element.
//!
//! The hard part is not the fold, it is the arena. A candidate list
//! over-approximates in two independent ways: a candidate may not be in the
//! set, and two candidates may denote the same value. A step therefore only
//! takes effect when the candidate is present **and** is not a duplicate of an
//! earlier present one – the same guard `Cardinality` uses, and the same one
//! Apalache builds in `SetOps.dedup`. The tests below pin both halves,
//! because either one missing is a wrong answer rather than a missing feature.

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome, SetupError};

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

// ======== a fold over a literal set ========

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

// ======== the arena's two over-approximations ========

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
/// missing feature – it is the reason `SetOps.dedup` exists in Apalache.
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

/// Folding a set is the same as its cardinality when the operator counts –
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

// ======== sequences ========

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

// ======== an accumulator that is not a scalar ========

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

// ======== state ========

/// A fold over a state variable's value, which is the case Apalache's
/// `FoldSetInInit` regression covers.
#[test]
fn a_fold_reads_the_state() {
    holds("x", ADD, "x \\in {1, 2}", "ApaFoldSet(Add, 0, {x, 3}) > 3");
}

// ======== the order-independence audit ========
//
// TLA+ specifies no fold order for a set, so `ApaFoldSet` only has a value
// when the operator's n-fold composition commutes. Before the audit, the
// encoder folded in candidate order while the evaluator folded in sorted
// order, and `F(a, b) == (a + 1) * (b + 1)` over `{3, 2}` answered `15` on
// one side and `16` on the other – a replay disagreement that was surfaced as
// "possibly spurious" rather than refused. The audit declines the fold
// outright; these tests pin both sides of that.

/// The reproducer: an operator whose composition is order-dependent –
/// `F(a, b) == (a + 1) * (b + 1)` folds `{2, 3}` to `16` in ascending order
/// and `{3, 2}` to `15` in written order. Before the audit the encoder
/// answered with the written order and the replay expected the sorted one.
/// It must be **declined**, never answered.
#[test]
fn a_non_ac_operator_over_a_set_declines() {
    let src = spec(
        "x",
        "F(a, b) == (a + 1) * (b + 1)",
        "x = 0",
        "ApaFoldSet(F, 0, {3, 2}) = 16",
    );
    let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
    let loaded = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = loaded.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&loaded, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    let err = bmc.check(0, &mut tm).expect_err("declines");
    let SetupError::Encode { why, .. } = &err else {
        panic!("expected an encode refusal, got {err}");
    };
    assert!(
        why.contains("associative and commutative"),
        "the refusal should name the audit: {why}"
    );
}

/// Subtraction is not commutative, so a two-element set declines too – every
/// order-sensitivity argument starts at two members.
#[test]
fn a_non_commutative_operator_declines_over_two_elements() {
    let src = spec("x", SUB, "x = 0", "ApaFoldSet(Sub, 0, {1, 2}) = -3");
    let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
    let loaded = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = loaded.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&loaded, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert!(bmc.check(0, &mut tm).is_err());
}

/// A singleton has one order, so the audit does not refuse it: any operator
/// folds a one-member set to exactly one value.
#[test]
fn a_singleton_set_folds_any_operator() {
    holds("x", SUB, "x = 0", "ApaFoldSet(Sub, 5, {2}) = 3");
}

/// An accumulator mentioned twice does not commute even under `+`:
/// `A(a, b) == a + a + b` composes to `2·(…)+b`, and the orders disagree.
#[test]
fn an_accumulator_twice_in_an_add_chain_declines() {
    let src = spec(
        "x",
        "A(a, b) == a + a + b",
        "x = 0",
        "ApaFoldSet(A, 0, {1, 2}) = 6",
    );
    let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
    let loaded = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = loaded.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&loaded, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert!(bmc.check(0, &mut tm).is_err());
}

/// `Max`- and `Min`-shaped conditionals are associative, commutative and
/// idempotent – more than order-independence needs.
#[test]
fn a_max_shaped_operator_folds() {
    holds(
        "x",
        "Max(a, b) == IF a > b THEN a ELSE b",
        "x = 0",
        "ApaFoldSet(Max, 0, {3, 1, 2}) = 3",
    );
    holds(
        "x",
        "Min(a, b) == IF a > b THEN b ELSE a",
        "x = 0",
        "ApaFoldSet(Min, 9, {3, 1, 2}) = 1",
    );
}

/// The function-update idiom: `[f EXCEPT ![x] = f[x] + 1]`. Each element is
/// folded once and writes only its own index, so every read of `f[x]` sees
/// the original value – order-independent. This is `Antipatterns.tla`'s
/// `addOneInCdm`.
#[test]
fn the_function_update_idiom_folds() {
    holds(
        "x",
        "A(p, q) == [p EXCEPT ![q] = p[q] + 1]\nf == [v \\in {\"a\", \"b\"} |-> 0]",
        "x = 0",
        "ApaFoldSet(A, f, DOMAIN f) = [v \\in DOMAIN f |-> 1]",
    );
}

/// An update whose value reads the whole accumulator does not commute.
#[test]
fn a_function_update_reading_the_whole_accumulator_declines() {
    let src = spec(
        "x",
        "A(p, q) == [p EXCEPT ![q] = Cardinality(DOMAIN p)]\nf == [v \\in {\"a\", \"b\"} |-> 0]",
        "x = 0",
        "ApaFoldSet(A, f, DOMAIN f) = f",
    );
    let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
    let loaded = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = loaded.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&loaded, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert!(bmc.check(0, &mut tm).is_err());
}

/// A fold that rebuilds a set – `FoldSetSet.tla`'s shape, and `RemakeSet`
/// from `Antipatterns.tla`.
#[test]
fn a_union_with_singletons_folds() {
    holds(
        "x",
        "A(p, q) == p \\cup {q}",
        "x = 0",
        "ApaFoldSet(A, {4}, {1, 1, 2, 3}) = {1, 2, 3, 4}",
    );
}

/// A fold whose step writes the accumulator at the **element's own key** –
/// `![p, q]` with `p == pair[1]`, `q == pair[2]`, over a product of two
/// sets – and reads the accumulator nowhere: each step depends on no other
/// step, so the fold is order-free (`FoldExcept.tla`'s `SubtractInLoop`,
/// two cells of Apalache's suite). The key must *be* the element:
/// `<<pair[1], pair[1]>>` names only its first component, so two elements
/// would write the same entry, and that still declines.
#[test]
fn a_fold_whose_step_writes_the_elements_own_key_is_order_free() {
    let init = "x = [p \\in 1..2, q \\in 1..2 |-> 0]";
    // The signature pins `pair`'s shape, as `FoldExcept.tla`'s does.
    let sig = "\\* @type: (<<Int, Int>> -> Int, <<Int, Int>>) => <<Int, Int>> -> Int;\n\
               W(f, pair) == [f EXCEPT ![pair[1], pair[2]] = pair[1] * 10 + pair[2]]";
    holds(
        "x",
        sig,
        init,
        "ApaFoldSet(W, x, {1, 2} \\X {1, 2}) = [p \\in 1..2, q \\in 1..2 |-> p * 10 + q]",
    );
    let src = spec(
        "x",
        "\\* @type: (<<Int, Int>> -> Int, <<Int, Int>>) => <<Int, Int>> -> Int;\n\
         W(f, pair) == [f EXCEPT ![pair[1], pair[1]] = 1]",
        init,
        "ApaFoldSet(W, x, {1, 2} \\X {1, 2}) = x",
    );
    let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
    let loaded = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = loaded.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&loaded, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    let err = bmc
        .check(0, &mut tm)
        .expect_err("a non-injective key declines");
    assert!(
        err.to_string().contains("associative and commutative"),
        "{err}"
    );
}
