//! `f[x \in S] == … f[…] …` — functions defined in terms of themselves.
//!
//! Ordinary TLA+, with no `RECURSIVE` keyword, and how Fibonacci, factorial
//! and every "sum of a sequence" is written. Inlining such a definition
//! reproduces the body inside itself; the only thing that stopped it was the
//! lowering budget, which is why these specifications reported *"lowering
//! exceeded its budget of 100000 steps"* rather than anything useful.
//!
//! Over a **finite** domain they need no fixpoint and no quantifier: the
//! function is an array, plus one equation per point of its domain saying what
//! it is there. The body is encoded once per point with the function itself in
//! scope, so `f[k-1]` inside it is a `select` on the very array being defined.
//!
//! The evaluator ties the same knot differently — repeated refinement until
//! nothing changes — so a counterexample here is confirmed by an
//! implementation that does not share the encoder's trick.

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome, Verification};

fn check(src: &str, depth: u32) -> Outcome {
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let loaded = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = loaded.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&loaded, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    bmc.check(depth, &mut tm).expect("checks")
}

fn spec(defs: &str, inv: &str) -> String {
    format!(
        r"
---- MODULE Rec ----
EXTENDS Integers
VARIABLE x
{defs}
Init == x = 0
Next == UNCHANGED x
Inv  == {inv}
====
"
    )
}

const FIB: &str = "f[k \\in 0..6] == IF k <= 1 THEN k ELSE f[k-1] + f[k-2]";

/// Every value of the sequence, not just the last: a definition that is right
/// only at the point the invariant asks about is not right.
#[test]
fn fibonacci() {
    assert_eq!(
        check(
            &spec(
                FIB,
                "/\\ f[0] = 0 /\\ f[1] = 1 /\\ f[2] = 1 /\\ f[3] = 2 \
                 /\\ f[4] = 3 /\\ f[5] = 5 /\\ f[6] = 8"
            ),
            1
        ),
        Outcome::NoViolationWithin(1)
    );
}

#[test]
fn a_wrong_claim_about_a_recursive_function_is_found() {
    assert_eq!(
        check(&spec(FIB, "f[6] = 9"), 1),
        Outcome::Violation { step: 0 }
    );
}

/// And that counterexample **replays**, through an evaluator that computes the
/// same function by repeated refinement rather than by equations over an
/// array. The two agreeing is the point.
#[test]
fn a_recursive_counterexample_replays() {
    let src = spec(FIB, "f[6] = 9");
    let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
    let loaded = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = loaded.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&loaded, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert_eq!(
        bmc.check(1, &mut tm).expect("checks"),
        Outcome::Violation { step: 0 }
    );
    assert_eq!(bmc.verification(), Some(&Verification::Replayed));
}

#[test]
fn factorial() {
    assert_eq!(
        check(
            &spec(
                "g[k \\in 1..5] == IF k = 1 THEN 1 ELSE k * g[k-1]",
                "g[5] = 120"
            ),
            1
        ),
        Outcome::NoViolationWithin(1)
    );
}

/// The recursion need not go downwards, and the definition order is not
/// guessed: each point is an equation, and the solver sorts it out.
#[test]
fn a_recursion_that_counts_upwards() {
    assert_eq!(
        check(
            &spec(
                "h[k \\in 0..3] == IF k = 3 THEN 0 ELSE h[k+1] + 1",
                "h[0] = 3"
            ),
            1
        ),
        Outcome::NoViolationWithin(1)
    );
}

/// Used twice, it must be the *same* function — one array, not two, or
/// `f[3] = f[3]` could come out false.
#[test]
fn two_uses_are_one_function() {
    assert_eq!(
        check(&spec(FIB, "f[3] = f[3]"), 1),
        Outcome::NoViolationWithin(1)
    );
    assert_eq!(
        check(&spec(FIB, "f[3] + f[4] = 5"), 1),
        Outcome::NoViolationWithin(1)
    );
}

/// A recursive function reading the state, which is the shape that makes this
/// worth having in a model checker rather than a calculator.
#[test]
fn a_recursive_function_over_the_state() {
    let src = r"
---- MODULE RecState ----
EXTENDS Integers
VARIABLE n
sum[k \in 0..4] == IF k = 0 THEN 0 ELSE k + sum[k-1]
Init == n = 0
Next == n' = n + 1
Inv  == sum[4] = 10
====
";
    assert_eq!(check(src, 3), Outcome::NoViolationWithin(3));
}

/// A plain function definition is untouched by any of this.
#[test]
fn a_plain_function_definition_is_unchanged() {
    assert_eq!(
        check(&spec("p[k \\in 1..3] == k * 10", "p[2] = 20"), 1),
        Outcome::NoViolationWithin(1)
    );
    assert_eq!(
        check(&spec("p[k \\in 1..3] == k * 10", "p[2] = 30"), 1),
        Outcome::Violation { step: 0 }
    );
}
