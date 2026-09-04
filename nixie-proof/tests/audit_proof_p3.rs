//! Regression tests for the `proof-p3` audit findings, exercised through
//! `nixie-proof`'s *public* API (as an external consumer of the crate would
//! use it), rather than the crate-internal unit tests already added
//! alongside each fix in `checker.rs` / `conversion.rs`.
//!
//! Findings covered:
//! 1. `checker.rs`: `CheckerConfig::verify_conclusions` now actually gates
//!    semantic conclusion checking instead of being silently ignored.
//! 2. `conversion.rs`: `FormatConverter::drat_to_alethe` derives structure
//!    from the real DRAT steps plus a caller-supplied input clause set,
//!    and refuses (rather than fabricates) when a clause's derivation
//!    can't be faithfully reconstructed.
//! 3. `lib.rs`: `premise` is now a public module, so `PremiseId` /
//!    `PremiseTracker` -- required by `CraigInterpolator::new`'s public
//!    constructor -- are nameable and constructible from outside the crate.

use nixie_proof::checker::{CheckError, CheckResult, Checkable, CheckerConfig};
use nixie_proof::conversion::{ConversionError, FormatConverter};
use nixie_proof::craig::{CraigInterpolator, InterpolantPartition, InterpolationConfig};
use nixie_proof::drat::DratProof;
use nixie_proof::premise::{PremiseId, PremiseTracker};
use nixie_proof::proof::Proof;
use nixie_proof::theory::TheoryRule;
use nixie_proof::{PremiseId as ReexportedPremiseId, PremiseTracker as ReexportedPremiseTracker};
use nixie_proof::{Proof as ReexportedProof, TheoryProof};

// ========  ========
// Finding 1: checker.rs verify_conclusions
// ========  ========

#[test]
fn verify_conclusions_default_off_accepts_semantically_bogus_proof() {
    // Public-API smoke test for the pre-existing (and still supported)
    // structural-only default behavior: without opting in, a Trans step
    // whose conclusion is unrelated to its premises is still accepted.
    let mut proof = TheoryProof::new();
    let s1 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= a b)");
    let s2 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= b c)");
    proof.add_step(TheoryRule::Trans, vec![s1, s2], "(= x y)");

    assert!(proof.check().is_valid());
}

#[test]
fn verify_conclusions_on_rejects_semantically_bogus_proof_via_public_api() {
    let mut proof = TheoryProof::new();
    let s1 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= a b)");
    let s2 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= b c)");
    proof.add_step(TheoryRule::Trans, vec![s1, s2], "(= x y)");

    let config = CheckerConfig {
        verify_conclusions: true,
        ..Default::default()
    };
    let result = proof.check_with_config(config);
    assert!(!result.is_valid());
    assert!(matches!(
        result,
        CheckResult::Invalid {
            error: CheckError::InvalidConclusion(_),
            ..
        }
    ));
}

#[test]
fn verify_conclusions_on_accepts_genuinely_valid_proof_via_public_api() {
    let mut proof = TheoryProof::new();
    let s1 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= a b)");
    let s2 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= b c)");
    proof.trans(s1, s2, "a", "c");

    let config = CheckerConfig {
        verify_conclusions: true,
        ..Default::default()
    };
    assert!(proof.check_with_config(config).is_valid());
}

// ========  ========
// Finding 2: conversion.rs drat_to_alethe
// ========  ========

#[test]
fn drat_to_alethe_marks_only_genuine_input_clauses_as_input() {
    let converter = FormatConverter::new();
    let mut drat = DratProof::new();
    drat.add_clause(vec![1, 2]);
    drat.add_clause(vec![-1, 3]);

    let input_clauses = vec![vec![1, 2], vec![-1, 3]];
    let alethe = converter
        .drat_to_alethe(&drat, &input_clauses)
        .expect("both clauses are genuine input clauses");

    assert_eq!(alethe.len(), 2);
    assert!(alethe.to_string().contains(":rule input"));
}

#[test]
fn drat_to_alethe_refuses_to_fabricate_resolution_premises() {
    // This clause is not present in the (empty) input set, so it is a
    // derived/learned clause. Plain DRAT carries no witness data for how it
    // was derived -- the converter must report this honestly rather than
    // guessing a resolution chain (the bug this finding was about).
    let converter = FormatConverter::new();
    let mut drat = DratProof::new();
    drat.add_clause(vec![1, 2]);

    let result = converter.drat_to_alethe(&drat, &[]);
    match result {
        Err(ConversionError::InformationLoss { .. }) => {}
        other => panic!(
            "expected InformationLoss for an unreconstructible derived clause, got {other:?}"
        ),
    }
}

// ========  ========
// Finding 3: lib.rs pub mod premise (CraigInterpolator public constructor)
// ========  ========

#[test]
fn craig_interpolator_is_constructible_via_the_public_premise_api() {
    // Before the fix, `premise` was a private module: `PremiseTracker`
    // (required by `CraigInterpolator::new`) was unnameable outside the
    // crate, so this constructor was effectively unusable by downstream
    // consumers even though it was `pub fn`.
    let mut tracker = PremiseTracker::new();
    let a = tracker.add_assertion("(= a b)");
    let b = tracker.add_assertion("(= c d)");

    let partition = InterpolantPartition::new(vec![a], vec![b]);
    let mut interpolator = CraigInterpolator::new(
        InterpolationConfig::default(),
        partition,
        PremiseTracker::new(),
    );

    // A trivial proof still round-trips through the public extract() API.
    let proof = Proof::new();
    let _ = interpolator.extract(&proof);

    // Also confirm the crate-root re-exports (used throughout the rest of
    // the crate's public API) name the exact same types.
    let _: ReexportedPremiseId = a;
    let _: ReexportedPremiseId = PremiseId(0);
    let _: ReexportedPremiseTracker = ReexportedPremiseTracker::new();
    let _: ReexportedProof = Proof::new();
}
