//! Positive-existential skolemization over the standard infinite sets
//! (issue #20, first piece).
//!
//! `\E x \in Nat : P(x)` in a position the solver is asked to **satisfy**
//! becomes a fresh constant with `x \in Nat /\ P(x)`. Polarity is the
//! soundness boundary: an existential under an odd number of negations is a
//! universal claim and must NOT be skolemized, while a *universal* under an
//! odd number of negations is an existential and may be.

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome};

fn claim(body: &str) -> Outcome {
    let src = format!(
        r#"
---- MODULE Claim ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x = 0
Next == UNCHANGED <<x>>
Inv  == {body}
====
"#
    );
    let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    bmc.check(0, &mut tm).expect("checks")
}

fn holds(body: &str) {
    assert_eq!(claim(body), Outcome::NoViolationWithin(0), "`{body}`");
}

fn fails(body: &str) {
    assert_eq!(claim(body), Outcome::Violation { step: 0 }, "`{body}`");
}

fn declines(body: &str) {
    let src = format!(
        r#"
---- MODULE Claim ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x = 0
Next == UNCHANGED <<x>>
Inv  == {body}
====
"#
    );
    let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert!(bmc.check(0, &mut tm).is_err(), "`{body}` should decline");
}

// ======== positive existentials, in an asserted formula ========

/// The witness idiom where it is genuinely one: `Init`'s existential. The
/// helper spec's `Init` is fixed, so the body here restates a witness form
/// as an invariant's *dual* instead; the direct form lives in the next test.
#[test]
fn a_positive_existential_over_nat_skolemizes() {
    // A **negated** existential in the invariant is the query's positive
    // existential (`~~E` in `~Inv`): skolemized and answered. `~\E y \in
    // Nat : y < x` holds – no natural is below zero.
    holds(r"~\E y \in Nat : y < x");
    // A negated existential over STRING, through the same shape.
    holds(r#"~\E s \in STRING : s # s"#);
}

/// A positive existential in `Init` is witnessed: an initial state exists
/// exactly when the witness and its membership do.
#[test]
fn a_witness_in_init_is_skolemized() {
    let src = r#"
---- MODULE Wit ----
EXTENDS Integers
VARIABLE x
Init == \E y \in Nat : x = y + 1
Next == UNCHANGED x
Inv == x >= 1
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert_eq!(
        bmc.check(0, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(0),
        "the witness y = 0 gives x = 1"
    );
}

// ======== polarity ========

/// An existential under a negation is a universal: `~\E y \in Nat : y < x`
/// with `x = 0` **holds**, and skolemizing it would answer the opposite.
/// A **plain positive** existential in the invariant is the query's
/// *universal* (`~Inv` doubles the negation), which no skolem can serve:
/// declined rather than enumerated over a guessed bound.
#[test]
fn a_plain_positive_existential_in_an_invariant_declines() {
    declines(r"\E y \in Nat : y > x");
}

/// A **positive** universal in the invariant is the query's existential
/// (the invariant enters negated), so it skolemizes: `\A y \in Nat : y >
/// x` at `x = 0` is refuted by the witness `y = 0`.
#[test]
fn an_invariants_universal_skolemizes_as_the_query_existential() {
    fails(r"\A y \in Nat : y > x");
    // ...and the true universal claim now holds, witnessed:
    holds(r"\A y \in Nat : y >= 0");
}

/// A negated implication arm flips polarity: in the invariant, `~(x < 0
/// => \A y \in Nat : y > x)`'s universal sits under two negations and the
/// claim is decidable via the finite reading; the infinite-set existential
/// arm of an implication in an *invariant* is the query's universal and
/// declines – pinned here so nobody "fixes" it into a wrong answer.
#[test]
fn implication_arms_carry_polarity() {
    // The antecedent false makes the implication true at x = 0; the
    // universal arm under the implication's flipped polarity is the
    // query's existential only when the arm is the *negated* one.
    holds(r"x < 0 => \A y \in {0, 1} : y >= 0");
    declines(r"x < 0 => \E y \in Nat : y < x");
}

/// An `IF` condition is both-polarity: an existential inside one is never
/// rewritten, and the encoding declines rather than guessing.
#[test]
fn ite_conditions_are_never_rewritten() {
    declines(r"IF \E y \in Nat : y < x THEN TRUE ELSE FALSE");
}

// ======== one witness per step ========

/// A witness stands for "some member **at the step the quantifier is
/// evaluated**". `\E k \in Nat : (k = 2 \/ k = 3) /\ x' = x + k` in `Next`
/// picks a `k` at every step, and `0 -> 2 -> 5` violates `x # 5` at step 2.
/// With one rigid witness for the whole unrolling, every step kept the same
/// `k` and the reachable sums were `0, c, 2c` – never 5 – so the checker
/// printed "no counterexample of 2 step(s) or fewer" (exit 0) for a
/// specification that has one. The same spec over the literal set `{2, 3}`
/// (enumerated exactly) found it, which is how the two were told apart.
#[test]
fn a_witness_is_picked_anew_at_every_step() {
    let src = r#"
---- MODULE Steps ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == \E k \in Nat : (k = 2 \/ k = 3) /\ x' = x + k
Inv  == x # 5
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    let out = bmc.check(2, &mut tm).expect("checks");
    assert_eq!(out, Outcome::Violation { step: 2 }, "{out:?}");
    // And the replay confirms it with the witnesses read back per state:
    // the evaluator saw `k` be 2 on the first step and 3 on the second.
    assert_eq!(
        bmc.verification(),
        Some(&nixie_tla_check::bmc::Verification::Replayed)
    );
    let trace = bmc.counterexample().expect("a trace");
    // The binder is renamed by the pass (`k#1`), so the witness is found by
    // its marker; it is one entry per state, and the two steps disagree.
    let witness = |i: usize| {
        trace.states[i]
            .iter()
            .find(|(n, _)| nixie_tla::lower::is_skolem_witness(n))
            .map(|(_, v)| v.clone())
    };
    let (first, second) = (witness(0), witness(1));
    assert!(matches!(first, Some(nixie_tla::Value::Int(_))), "{trace:?}");
    assert_ne!(first, second, "one witness per step: {trace:?}");
    assert!(
        matches!(trace.states[2].get("x"), Some(nixie_tla::Value::Int(i)) if *i == 5.into()),
        "{trace:?}"
    );
    // A witness is the encoding's own name, not a parameter of the
    // specification: it stays out of the trace's header.
    let itf = bmc.counterexample_itf("Steps").expect("ITF");
    assert_eq!(itf["vars"], serde_json::json!(["x"]), "{itf}");
    let params: Vec<String> = itf["params"]
        .as_array()
        .expect("params")
        .iter()
        .filter_map(|p| p.as_str().map(std::string::ToString::to_string))
        .collect();
    assert!(
        params
            .iter()
            .all(|p| !nixie_tla::lower::is_skolem_witness(p)),
        "{itf}"
    );
}

/// The name is the encoder's contract with the skolemizing pass: whatever
/// the pass mints is recognised, and nothing else is.
#[test]
fn the_witness_marker_is_recognised_exactly() {
    use nixie_tla::lower::is_skolem_witness;
    assert!(is_skolem_witness("k!skolem1"));
    assert!(is_skolem_witness("x#2!skolem12"));
    assert!(!is_skolem_witness("k!skolem"), "no counter");
    assert!(!is_skolem_witness("k!skolemx"), "not a counter");
    assert!(!is_skolem_witness("k"), "a plain name");
    assert!(!is_skolem_witness("N"), "a CONSTANT");
}

/// `\E d \in Nat \ {0}` is skolemized like `\E d \in Nat`: the difference
/// cannot be enumerated any more than `Nat` can, and the witness keeps its
/// membership as a constraint, encoded structurally – so `x` is at least 1.
/// Left to the enumeration it declined as "`Nat` used as a value", which is
/// what refused `FoldExcept.tla`'s `Next` (`\E delta \in Nat \ {0}`). And
/// the replay reads the membership structurally too: a correct
/// counterexample came back `Unknown` while the evaluator tried to
/// materialise `Nat \ {0}`.
#[test]
fn a_difference_of_a_standard_set_skolemizes_as_the_set_does() {
    for (body, want) in [
        ("x >= 1", Outcome::NoViolationWithin(0)),
        ("x # 0", Outcome::NoViolationWithin(0)),
        ("x = 0", Outcome::Violation { step: 0 }),
        ("x < 0", Outcome::Violation { step: 0 }),
    ] {
        let src = format!(
            r#"
---- MODULE Delta ----
EXTENDS Integers
VARIABLE
    \* @type: Int;
    x
Init == \E d \in Nat \ {{0}}: x = d
Next == UNCHANGED <<x>>
Inv  == {body}
====
"#
        );
        let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
        let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
        let module = spec.root_module().expect("has a root module");
        let mut tm = TermManager::new();
        let mut bmc =
            Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
        assert_eq!(bmc.check(0, &mut tm).expect("checks"), want, "`{body}`");
    }
}
