//! Reading a counterexample back, and checking it.
//!
//! A `Sat` answer to the bounded query *is* a counterexample, and the checker
//! used to throw it away: `Outcome::Violation` carried a step number and
//! nothing else. That left the one hop in the pipeline with no independent
//! check on it. Parsing is measured against SANY, lowering against TLC, the
//! encoding against the evaluator — and the verdict itself was taken on the
//! solver's word.
//!
//! Replaying closes that loop. The states behind a `Sat` are decoded into TLA+
//! values and handed to `nixie-tla`'s evaluator, which is a separate
//! implementation of the language: `Init` must hold in the first state, `Next`
//! between each pair, the configuration's constraints throughout, and the
//! invariant must actually be `FALSE` at the end. A trace that replays has
//! been confirmed without the solver's help.

use nixie_core::TermManager;
use nixie_tla::Value;
use nixie_tla_check::bmc::{Bmc, Outcome, Verification};

fn run(src: &str, depth: u32) -> (Outcome, Option<String>, Option<Verification>) {
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let loaded = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = loaded.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&loaded, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    let out = bmc.check(depth, &mut tm).expect("checks");
    let trace = bmc.counterexample().map(std::string::ToString::to_string);
    (out, trace, bmc.verification().cloned())
}

/// The states of a counterexample, as `(name, value)` pairs per state.
fn states(src: &str, depth: u32) -> Vec<Vec<(String, Value)>> {
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let loaded = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = loaded.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&loaded, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert!(
        matches!(bmc.check(depth, &mut tm), Ok(Outcome::Violation { .. })),
        "expected a violation"
    );
    let t = bmc.counterexample().expect("a decoded trace");
    t.states
        .iter()
        .map(|s| {
            let mut v: Vec<(String, Value)> =
                s.iter().map(|(k, x)| (k.clone(), x.clone())).collect();
            v.sort_by(|a, b| a.0.cmp(&b.0));
            v
        })
        .collect()
}

const COUNTER: &str = r"
---- MODULE Counter ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv  == x < 3
====
";

// ---- the trace is the behaviour ----

/// The counterexample to `x < 3` is `0, 1, 2, 3`: four states, three steps,
/// and every value pinned.
#[test]
fn a_counting_trace_is_the_behaviour() {
    let st = states(COUNTER, 5);
    assert_eq!(st.len(), 4, "four states for a three-step counterexample");
    for (i, s) in st.iter().enumerate() {
        assert_eq!(
            s.as_slice(),
            [("x".to_string(), Value::Int(i as i128))],
            "state {i}"
        );
    }
}

/// And it replays: `Init` holds at the start, `Next` between each pair, and
/// the invariant is `FALSE` at the end. Nothing here consults the solver.
#[test]
fn a_counting_trace_replays() {
    let (out, trace, v) = run(COUNTER, 5);
    assert_eq!(out, Outcome::Violation { step: 3 });
    assert_eq!(v, Some(Verification::Replayed));
    let trace = trace.expect("a decoded trace");
    assert!(trace.contains("State 3:"), "{trace}");
    assert!(trace.contains("x = 3"), "{trace}");
}

/// A violation in the initial state is a one-state trace, not a zero-state
/// one: the state the invariant fails in is always there.
#[test]
fn an_initial_violation_has_one_state() {
    let st = states(
        r"
---- MODULE Bad ----
EXTENDS Integers
VARIABLE x
Init == x = 5
Next == UNCHANGED x
Inv  == x < 3
====
",
        3,
    );
    assert_eq!(st.len(), 1);
    assert_eq!(st[0].as_slice(), [("x".to_string(), Value::Int(5))]);
}

/// A `CONSTANT` is in every state of the trace, with the same value: it is
/// what the solver chose for it, and the replay needs it to evaluate anything
/// that mentions it.
#[test]
fn a_constant_is_carried_in_the_trace() {
    let st = states(
        r"
---- MODULE WithConst ----
EXTENDS Integers
CONSTANT N
VARIABLE x
Init == x = 0 /\ N = 2
Next == x' = x + 1
Inv  == x # N
====
",
        4,
    );
    assert!(st.len() >= 2, "{st:?}");
    for s in &st {
        assert!(
            s.contains(&("N".to_string(), Value::Int(2))),
            "N missing from a state: {s:?}"
        );
    }
}

// ---- values of every shape the decoder handles ----

#[test]
fn a_record_valued_variable_decodes() {
    let st = states(
        r"
---- MODULE Rec ----
EXTENDS Integers
VARIABLE r
Init == r = [a |-> 1, b |-> TRUE]
Next == UNCHANGED r
Inv  == r.a = 2
====
",
        1,
    );
    let want = Value::Record(
        [
            ("a".to_string(), Value::Int(1)),
            ("b".to_string(), Value::Bool(true)),
        ]
        .into_iter()
        .collect(),
    );
    assert_eq!(st[0].as_slice(), [("r".to_string(), want)]);
}

/// A tuple decodes, and the second component is **wrong** — recorded here
/// because it is a real defect in the solver's model, not in this decoder.
///
/// `docs/studies/2026-09-14-model-completion-overrides-datatype-fields.md` has
/// the four-line reproducer: assert `@t1(t) = 1` and `@t2(t) = "a"`, and the
/// model answers `@t1(t) -> 1`, `@t2(t) -> ""` while evaluating the assertion
/// `@t2(t) = "a"` to `TRUE`. The verdict is right and the model contradicts
/// itself; a `(get-value (@t2 t))` would answer `""` for a term the assertions
/// pin to `"a"`.
///
/// This is exactly what replaying is for. The trace decodes, the replay says
/// `Init` is FALSE, and the disagreement is visible instead of being carried
/// silently inside a counterexample nobody reads.
#[test]
fn a_tuple_field_the_query_did_not_probe_comes_back_defaulted() {
    let (out, _, v) = run(
        r#"
---- MODULE Tup ----
EXTENDS Integers
VARIABLE t
Init == t = <<1, "a">>
Next == UNCHANGED t
Inv  == t[1] = 2
====
"#,
        1,
    );
    assert_eq!(out, Outcome::Violation { step: 0 });
    match v {
        Some(Verification::NotReplayed(why)) => {
            assert!(why.contains("`Init`"), "{why}");
        }
        other => panic!("expected the replay to catch the defaulted field, got {other:?}"),
    }
}

#[test]
fn a_set_valued_variable_decodes() {
    let st = states(
        r"
---- MODULE Sets ----
EXTENDS Integers
VARIABLE s
Init == s = {1, 2}
Next == UNCHANGED s
Inv  == 3 \in s
====
",
        1,
    );
    let want = Value::set([Value::Int(1), Value::Int(2)]);
    assert_eq!(st[0].as_slice(), [("s".to_string(), want)]);
}

/// A set that grows across steps — the shape the arena cannot express at all,
/// and the one where the solver's own extensionality witnesses show up in the
/// membership atoms. They are not TLA+ values and must not reach the trace.
#[test]
fn a_growing_set_decodes_without_solver_scaffolding() {
    let st = states(
        r"
---- MODULE Grow ----
EXTENDS Integers
VARIABLE s
Init == s = {}
Next == s' = s \cup {1}
Inv  == ~(1 \in s)
====
",
        4,
    );
    assert_eq!(st.len(), 2, "{st:?}");
    assert_eq!(st[0].as_slice(), [("s".to_string(), Value::set([]))]);
    assert_eq!(
        st[1].as_slice(),
        [("s".to_string(), Value::set([Value::Int(1)]))]
    );
}

// ---- what is not verified yet, recorded rather than assumed ----

/// A failing `Assert` is reported as a violation and **cannot** be replayed,
/// and the two facts belong together. The encoder reads `TLC!Assert`'s `ELSE`
/// branch — `CHOOSE v : TRUE` — as an unspecified Boolean, which is what TLA+
/// says it is; the evaluator refuses to give a failing `Assert` any value at
/// all, which is also right, because TLC's answer is to halt. So the trace is
/// decoded and the replay declines it, by name.
#[test]
fn a_failing_assert_is_not_replayable() {
    let (out, _, v) = run(
        r#"
---- MODULE Asserted ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 3
Next == UNCHANGED x
Inv  == Assert(x = 4, "x is not 4")
====
"#,
        1,
    );
    assert_eq!(out, Outcome::Violation { step: 0 });
    match v {
        Some(Verification::NotReplayed(why)) => {
            assert!(why.contains("Assert"), "{why}");
        }
        other => panic!("expected a replay refusal naming `Assert`, got {other:?}"),
    }
}

/// A function-valued variable is decoded from the `select` terms the query
/// built, because `Model::eval` has no case for the array theory — a `select`
/// this decoder builds itself would evaluate to itself and look unconstrained.
/// Where a point was never selected the value is genuinely arbitrary and is
/// completed with the sort's default, which is what makes a total TLA+
/// function out of a partial model.
///
/// The consequence is recorded here rather than left to be discovered: a
/// function whose graph the query never probed comes back as defaults, so it
/// does not replay. Extending `Model::eval` with `select`/`store` is the fix,
/// and it belongs in the solver.
#[test]
fn a_function_built_by_init_is_not_replayable_yet() {
    let (out, _, v) = run(
        r"
---- MODULE Fun ----
EXTENDS Integers
VARIABLE f
Init == f = [i \in {1, 2} |-> i]
Next == UNCHANGED f
Inv  == f[2] = 1
====
",
        1,
    );
    assert_eq!(out, Outcome::Violation { step: 0 });
    assert!(
        matches!(
            v,
            Some(Verification::NotReplayed(_) | Verification::NotDecoded(_))
        ),
        "expected the known array-model gap, got {v:?}"
    );
}
