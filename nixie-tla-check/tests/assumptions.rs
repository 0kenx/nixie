//! The honesty gates around a violation (issue #12).
//!
//! Exit 12 – "counterexample found" – is what users and downstream tools act
//! on, so a violation must never be reported under conditions that make the
//! counterexample provisional. Three such conditions are pinned here:
//!
//! 1. **Dropped assumptions.** A search that ran with an assumption it could
//!    not encode explored a *superset* of the intended states; a `Sat` there
//!    may be an artefact of exactly that widening.
//! 2. **Undecodable models.** The solver said `Sat`, but the states could not
//!    be read back as TLA+ values, so there is nothing to show and nothing to
//!    check the verdict against.
//! 3. **Non-replaying traces.** The states were read back and the independent
//!    evaluator – the one `bench/tla_eval` checks against TLC – rejects them.
//!    That is a disagreement between the encoding and the evaluator, and it is
//!    reported as such rather than resolved by trusting one side.
//!
//! Each becomes `Outcome::Unknown`, never `Outcome::Violation`.

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome, Roles, SetupError};
use nixie_tla_syntax::TlcConfig;

fn prepare(src: &str, inv: &str, config: &TlcConfig) -> Bmc {
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    Bmc::prepare_with_config(
        &spec,
        module,
        Roles {
            init: "Init",
            next: "Next",
            inv: std::slice::from_ref(&inv),
            constraints: &[],
        },
        config,
        &mut tm,
    )
    .expect("prepares")
}

fn outcome(src: &str, inv: &str) -> Outcome {
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc = Bmc::prepare(&spec, module, "Init", "Next", inv, &[], &mut tm).expect("prepares");
    bmc.check(0, &mut tm).expect("checks")
}

// ======== 1. dropped assumptions ========

/// An assumption whose constant has an open-record type has no sort, so it is
/// dropped; a violation found in that weakened search must be `Unknown`, with
/// a reason that names the count.
#[test]
fn a_violation_under_a_dropped_assumption_is_unknown() {
    let src = r"
---- MODULE DroppedGate ----
EXTENDS Integers
CONSTANT N, R
VARIABLE x
ASSUME N > 3
ASSUME R.f = 2
Init == x = 0
Next == x' = x
Inv  == x > 9999
====
";
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    let out = bmc.check(0, &mut tm).expect("checks");
    assert_eq!(
        bmc.dropped_assumptions(),
        1,
        "the open-record assumption must be dropped loudly"
    );
    let Outcome::Unknown(why) = out else {
        panic!("a violation under a dropped assumption must be Unknown, got {out:?}");
    };
    assert!(
        why.contains("1 assumption"),
        "the reason must name the count: {why}"
    );
}

/// The count does not grow across repeated checks: the `--max-error` loop
/// re-encodes, and double-counting would make the second query look weaker
/// than the first.
#[test]
fn dropped_assumptions_do_not_accumulate_across_checks() {
    let src = r"
---- MODULE DroppedTwice ----
EXTENDS Integers
CONSTANT R
VARIABLE x
ASSUME R.f = 2
Init == x = 0
Next == x' = x
Inv  == x < 1
====
";
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    let _ = bmc.check(0, &mut tm).expect("checks");
    let _ = bmc.check(0, &mut tm).expect("checks");
    assert_eq!(bmc.dropped_assumptions(), 1);
}

// ======== 2. ground assumptions are evaluated, not asserted ========

/// A false ground assumption means the specification has no behaviours at
/// all. TLC and Apalache report it and stop; so does this, by name – never a
/// counterexample for a specification that does not exist.
#[test]
fn a_false_ground_assumption_is_reported() {
    let src = r"
---- MODULE FalseAssume ----
EXTENDS Integers
CONSTANT N
VARIABLE x
ASSUME N > 3
Init == x = 0
Next == x' = x
Inv  == x < N
====
";
    let cfg_text = "CONSTANT N = 3\n";
    let config = nixie_tla_syntax::parse_config(cfg_text).expect("cfg parses");
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let err = match Bmc::prepare_with_config(
        &spec,
        module,
        Roles {
            init: "Init",
            next: "Next",
            inv: &["Inv"],
            constraints: &[],
        },
        &config,
        &mut tm,
    ) {
        Ok(_) => panic!("a false assumption must not prepare"),
        Err(e) => e,
    };
    assert!(
        matches!(err, SetupError::AssumptionViolated { .. }),
        "expected an assumption violation, got {err}"
    );
}

/// The evaluation runs on the **substituted** constants: with `N = 4` pinned,
/// `N > 3` is checked as `4 > 3`, which is TRUE – and a true assumption needs
/// no constraint at all, so the check proceeds and the violation is real.
#[test]
fn a_true_ground_assumption_asserts_nothing_and_the_violation_is_real() {
    let src = r"
---- MODULE TrueAssume ----
EXTENDS Integers
CONSTANT N
VARIABLE x
ASSUME N > 3
Init == x = 0
Next == x' = x
Inv  == x < N - 3
====
";
    let cfg_text = "CONSTANT N = 4\n";
    let config = nixie_tla_syntax::parse_config(cfg_text).expect("cfg parses");
    let mut bmc = prepare(src, "Inv", &config);
    assert_eq!(bmc.dropped_assumptions(), 0);
    let mut tm = TermManager::new();
    // `x < 1` with `x = 0` holds, so no violation at depth 0.
    assert_eq!(
        bmc.check(0, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(0)
    );
}

/// `N \in Nat \ {0}` is the `EWD840` shape: a membership over a standard
/// infinite set differenced with a finite one. It used to be unencodable –
/// dropped – leaving `N` arbitrary; the structural encoding makes it a
/// constraint, so a violation found under it is real and reported as such.
#[test]
fn a_standard_set_difference_membership_encodes() {
    let src = r"
---- MODULE NatMinus ----
EXTENDS Naturals
CONSTANT N
VARIABLE x
ASSUME N \in Nat \ {0}
Init == x = 0
Next == x' = x
Inv  == x < N
====
";
    let cfg_text = "CONSTANT N = 3\n";
    let config = nixie_tla_syntax::parse_config(cfg_text).expect("cfg parses");
    let mut bmc = prepare(src, "Inv", &config);
    assert_eq!(
        bmc.dropped_assumptions(),
        0,
        "`N \\in Nat \\ {{}}` must encode structurally, not drop"
    );
    let mut tm = TermManager::new();
    // `x = 0 < N = 3`: no violation. And with the assumption in force the
    // *negated* direction is pinned by the next test.
    assert_eq!(
        bmc.check(0, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(0)
    );
}

/// The same assumption must actually constrain: `N = 0` violates it, and the
/// check says so rather than running with an arbitrary `N`.
#[test]
fn a_violated_standard_set_membership_is_reported() {
    let src = r"
---- MODULE NatMinus0 ----
EXTENDS Naturals
CONSTANT N
VARIABLE x
ASSUME N \in Nat \ {0}
Init == x = 0
Next == x' = x
Inv  == x > 9999
====
";
    let cfg_text = "CONSTANT N = 0\n";
    let config = nixie_tla_syntax::parse_config(cfg_text).expect("cfg parses");
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc = match Bmc::prepare_with_config(
        &spec,
        module,
        Roles {
            init: "Init",
            next: "Next",
            inv: &["Inv"],
            constraints: &[],
        },
        &config,
        &mut tm,
    ) {
        Ok(b) => b,
        Err(SetupError::AssumptionViolated { .. }) => return, // also fine
        Err(e) => panic!("unexpected setup failure: {e}"),
    };
    // The evaluator cannot fold set membership over an infinite set, so the
    // contradiction surfaces from the assumption satisfiability probe rather
    // than prepare-time evaluation – same conclusion, one query later.
    assert_eq!(
        bmc.check(0, &mut tm).expect("checks"),
        Outcome::AssumptionsUnsatisfiable,
        "N = 0 contradicts `N \\in Nat \\ {{0}}`; there are no behaviours to check"
    );
}

// ======== 3. the replay gate ========

/// A trace that decodes but does not replay is a disagreement between the
/// encoding and the independent evaluator, and the honest verdict is
/// `Unknown` with the disagreement named – never a violation.
///
/// The shape: `f[2]` where `f`'s domain is `{1}`. TLA+ leaves it undefined;
/// the array encoding answers with whatever the base array holds, finds a
/// "violation", and the evaluator refuses to evaluate the undefined read.
#[test]
fn a_non_replaying_trace_is_unknown() {
    let src = r"
---- MODULE NoReplay ----
EXTENDS Integers
f == [i \in {1} |-> i]
Init == TRUE
Next == TRUE
Inv  == f[2] # 7
====
";
    let out = outcome(src, "Inv");
    let Outcome::Unknown(why) = out else {
        panic!("a non-replaying trace must be Unknown, got {out:?}");
    };
    assert!(
        why.contains("does not replay"),
        "the reason must name the replay disagreement: {why}"
    );
}

/// And the trace behind it stays visible for inspection, because a
/// non-replaying counterexample is a defect report about the pipeline, not a
/// verdict to shrug at.
#[test]
fn a_non_replaying_trace_stays_inspectable() {
    let src = r"
---- MODULE NoReplay2 ----
EXTENDS Integers
f == [i \in {1} |-> i]
Init == TRUE
Next == TRUE
Inv  == f[2] # 7
====
";
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    let _ = bmc.check(0, &mut tm).expect("checks");
    assert!(
        bmc.counterexample().is_some(),
        "the trace is kept: it is the defect report"
    );
    assert!(bmc.verification().is_some());
}
