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

/// A tuple decodes, both components. This used to come back
/// `<<1, "">>`: the solver's model had no value for a string-sorted term
/// pinned only by an equality, so a default was installed that contradicted
/// the assertion. The replay caught it, and
/// `docs/studies/2026-09-14-model-completion-overrides-datatype-fields.md`
/// records the fix.
#[test]
fn a_tuple_valued_variable_decodes() {
    let st = states(
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
    let want = Value::Tuple(vec![Value::Int(1), Value::Str("a".into())]);
    assert_eq!(st[0].as_slice(), [("t".to_string(), want)]);
}

/// A **function** built by `Init` decodes, point by point. This used to be
/// impossible: an array-sorted term had no model value at all and
/// `Model::eval` could not reduce a `select`, so every point looked
/// unconstrained and came back as the sort's default. See
/// `docs/studies/2026-09-14-no-model-for-array-variables.md`.
#[test]
fn a_function_built_by_init_decodes() {
    let st = states(
        r"
---- MODULE Fun ----
EXTENDS Integers
VARIABLE f
Init == f = [i \in {1, 2} |-> i * 10]
Next == UNCHANGED f
Inv  == f[2] = 1
====
",
        1,
    );
    // A function on `1..n` is a tuple in TLA+, and `Value::fun` normalises it.
    let want = Value::Tuple(vec![Value::Int(10), Value::Int(20)]);
    assert_eq!(st[0].as_slice(), [("f".to_string(), want)]);
}

/// A **sequence**-valued variable: the shape `intent`'s generated
/// specifications are built on (`history : Seq(Str)`, grown by `Append`).
#[test]
fn a_sequence_valued_variable_decodes() {
    let st = states(
        r#"
---- MODULE Seqs ----
EXTENDS Integers, Sequences
VARIABLE h
Init == h = <<>>
Next == h' = Append(h, "x")
Inv  == Len(h) < 2
====
"#,
        4,
    );
    assert_eq!(st.len(), 3, "{st:?}");
    assert_eq!(st[0].as_slice(), [("h".to_string(), Value::Tuple(vec![]))]);
    assert_eq!(
        st[2].as_slice(),
        [(
            "h".to_string(),
            Value::Tuple(vec![Value::Str("x".into()), Value::Str("x".into())])
        )]
    );
}
