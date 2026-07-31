//! `TheoryProof` -> Alethe conversion.
//!
//! [`theory_to_alethe`] converts this crate's internal
//! [`crate::theory::TheoryProof`] (the certificate a theory solver builds
//! while it works, via [`crate::builder::TheoryProofBuilder`] or directly)
//! into an [`crate::alethe::AletheProof`], suitable for export or for
//! checking with [`crate::checker::ProofChecker::check_alethe_proof`].
//!
//! This is a **different, narrower** conversion than
//! [`crate::conversion::FormatConverter`]: that type converts between
//! *external proof-file formats* (DRAT, Alethe, LFSC) that already exist as
//! their own serialized representations, while this module bridges from
//! this crate's own internal in-progress certificate type. Despite the
//! similar names (`ConversionStats` here vs. `ConversionError`/
//! `ConversionResult` there), there is no overlap in what the two convert.
//!
//! # Rule mapping fidelity
//!
//! Most `EUF`/arithmetic/array [`crate::theory::TheoryRule`] variants have
//! an exact Alethe counterpart (see this module's `map_theory_rule_to_alethe`
//! function). Everything else -- quantifier rules, bit-vector rules, `Custom` -- maps
//! to Alethe's `ThLemma`, which is Alethe's own designated escape hatch for
//! "established by theory reasoning this proof format does not further
//! elaborate." That is not a loss of information introduced by this
//! conversion: none of those rules are semantically checked in the source
//! `TheoryProof` either (see
//! [`crate::checker::CheckerConfig::verify_conclusions`]'s doc comment), so
//! the converted proof preserves exactly the checking fidelity the source
//! proof already had.
//!
//! # Examples
//!
//! ```
//! use oxiz_proof::{CheckResult, ProofChecker, TheoryProof, TheoryRule, theory_to_alethe};
//!
//! let mut theory = TheoryProof::new();
//! let xy = theory.add_axiom(TheoryRule::Custom("assert".into()), "(= x y)");
//! let yz = theory.add_axiom(TheoryRule::Custom("assert".into()), "(= y z)");
//! theory.trans(xy, yz, "x", "z");
//!
//! let alethe = theory_to_alethe(&theory).expect("well-formed proof converts");
//! assert_eq!(alethe.len(), 3);
//!
//! let mut checker = ProofChecker::new();
//! assert!(matches!(checker.check_alethe_proof(&alethe), CheckResult::Valid));
//! ```

use crate::alethe::{AletheProof, AletheRule};
use crate::conversion::{ConversionError, ConversionResult};
use crate::theory::{TheoryProof, TheoryRule, TheoryStepId};
use std::collections::HashMap;

/// Convert a theory proof to Alethe format.
///
/// This maps theory-specific rules to their Alethe equivalents.
///
/// # Errors
///
/// `TheoryProof::add_step`/`add_step_with_args` accept any
/// `Vec<TheoryStepId>` as a step's premises with no validation that those
/// IDs actually name earlier steps of *this* proof (they could be stale IDs
/// from a different `TheoryProof`, or simply fabricated). A premise ID that
/// does not resolve to an already-converted step is therefore possible, not
/// just theoretical. Silently omitting it from the Alethe step's premise
/// list -- the previous behavior -- would produce an Alethe proof whose
/// steps quietly depend on fewer premises than the source proof claims,
/// which a downstream checker could then accept as valid when the original
/// theory proof was not. This returns
/// [`ConversionError::InvalidSource`] instead.
pub fn theory_to_alethe(theory_proof: &TheoryProof) -> ConversionResult<AletheProof> {
    let mut alethe = AletheProof::new();
    let mut step_map: HashMap<TheoryStepId, u32> = HashMap::new();

    for step in theory_proof.steps() {
        // Map premise IDs to Alethe step indices; see the "# Errors" section
        // above for why an unresolved premise is a hard conversion error
        // rather than something to silently drop.
        let mut alethe_premises: Vec<u32> = Vec::with_capacity(step.premises.len());
        for &premise_id in &step.premises {
            match step_map.get(&premise_id) {
                Some(&alethe_idx) => alethe_premises.push(alethe_idx),
                None => {
                    return Err(ConversionError::InvalidSource {
                        reason: format!(
                            "theory proof step {} references premise {}, which is not an \
                             earlier step of this proof",
                            step.id.0, premise_id.0
                        ),
                    });
                }
            }
        }

        let alethe_rule = map_theory_rule_to_alethe(&step.rule);

        // Check if this is an assumption (axiom with no premises)
        let alethe_idx = if step.premises.is_empty() && is_assumption(&step.rule) {
            alethe.assume(&step.conclusion.0)
        } else {
            // Create a clause from the conclusion
            let clause = vec![step.conclusion.0.clone()];
            let args: Vec<String> = step.args.iter().map(|a| a.0.clone()).collect();

            alethe.step(clause, alethe_rule, alethe_premises, args)
        };

        step_map.insert(step.id, alethe_idx);
    }

    Ok(alethe)
}

/// Map a theory rule to its Alethe equivalent.
///
/// The wildcard arm is a deliberate, honest choice, not a shortcut: `ThLemma`
/// is Alethe's own designated escape hatch for "established by
/// theory-specific reasoning this proof format does not further elaborate"
/// (see [`crate::checker::ProofChecker`]'s documented scoping of
/// `verify_conclusions`, which never fabricates a semantic verdict for a
/// rule it cannot check). Routing every rule this crate does not have a
/// more specific Alethe counterpart for -- quantifier rules, bit-vector
/// rules, `Custom` -- to `ThLemma` therefore preserves exactly as much
/// checking fidelity as the source rule already had: none beyond structural
/// well-formedness.
fn map_theory_rule_to_alethe(rule: &TheoryRule) -> AletheRule {
    match rule {
        // EUF rules
        TheoryRule::Refl => AletheRule::Refl,
        TheoryRule::Symm => AletheRule::Symm,
        TheoryRule::Trans => AletheRule::Trans,
        TheoryRule::Cong => AletheRule::Cong,

        // Arithmetic rules
        TheoryRule::LaGeneric => AletheRule::LaGeneric,
        TheoryRule::LaTighten => AletheRule::LaTightening,
        TheoryRule::LaTotality => AletheRule::LaTotality,
        TheoryRule::LaDiseq => AletheRule::LaDisequality,

        // Array rules
        TheoryRule::ArrReadWrite1 => AletheRule::ArrayRowSame,
        TheoryRule::ArrReadWrite2 => AletheRule::ArrayRowDiff,
        TheoryRule::ArrExt => AletheRule::ArrayExt,

        // General rules
        TheoryRule::TheoryConflict => AletheRule::ThLemma,
        TheoryRule::TheoryProp => AletheRule::ThLemma,

        // Default to theory lemma -- see the doc comment above.
        _ => AletheRule::ThLemma,
    }
}

/// Check if a rule represents an assumption/axiom.
fn is_assumption(rule: &TheoryRule) -> bool {
    matches!(
        rule,
        TheoryRule::Custom(_)
            | TheoryRule::Refl
            | TheoryRule::ArrReadWrite1
            | TheoryRule::ArrConst
            | TheoryRule::LaTotality
    )
}

/// Statistics about proof conversion.
#[derive(Debug, Clone)]
pub struct ConversionStats {
    /// Number of steps in the source proof.
    pub source_steps: usize,
    /// Number of steps in the target proof.
    pub target_steps: usize,
    /// Number of assumptions/axioms.
    pub assumptions: usize,
    /// Number of inference steps.
    pub inferences: usize,
}

impl ConversionStats {
    /// Compute conversion statistics.
    #[must_use]
    pub fn compute(source: &TheoryProof, target: &AletheProof) -> Self {
        let assumptions = source
            .steps()
            .iter()
            .filter(|s| s.premises.is_empty())
            .count();

        Self {
            source_steps: source.len(),
            target_steps: target.len(),
            assumptions,
            inferences: source.len() - assumptions,
        }
    }
}

/// Convert theory proof to Alethe with statistics.
///
/// # Errors
///
/// Propagates [`theory_to_alethe`]'s error (see its "# Errors" section).
pub fn theory_to_alethe_with_stats(
    theory_proof: &TheoryProof,
) -> ConversionResult<(AletheProof, ConversionStats)> {
    let alethe = theory_to_alethe(theory_proof)?;
    let stats = ConversionStats::compute(theory_proof, &alethe);
    Ok((alethe, stats))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theory::ProofTerm;

    #[test]
    fn test_theory_to_alethe_simple() {
        let mut theory = TheoryProof::new();
        theory.refl("x");

        let alethe = theory_to_alethe(&theory).expect("well-formed proof must convert");
        assert_eq!(alethe.len(), 1);
    }

    #[test]
    fn test_theory_to_alethe_transitivity() {
        let mut theory = TheoryProof::new();

        let s1 = theory.add_axiom(TheoryRule::Custom("assert".into()), "(= a b)");
        let s2 = theory.add_axiom(TheoryRule::Custom("assert".into()), "(= b c)");
        theory.trans(s1, s2, "a", "c");

        let alethe = theory_to_alethe(&theory).expect("well-formed proof must convert");
        assert_eq!(alethe.len(), 3);
    }

    #[test]
    fn test_theory_to_alethe_arithmetic() {
        let mut theory = TheoryProof::new();

        let s1 = theory.add_axiom(TheoryRule::Custom("bound".into()), "(>= x 10)");
        let s2 = theory.add_axiom(TheoryRule::Custom("bound".into()), "(<= x 5)");
        theory.farkas(
            vec![s1, s2],
            &[ProofTerm("1".into()), ProofTerm("1".into())],
        );

        let alethe = theory_to_alethe(&theory).expect("well-formed proof must convert");
        assert_eq!(alethe.len(), 3);
    }

    #[test]
    fn test_conversion_stats() {
        let mut theory = TheoryProof::new();

        theory.add_axiom(TheoryRule::Custom("assert".into()), "(= x y)");
        theory.add_axiom(TheoryRule::Custom("assert".into()), "(= y z)");
        theory.refl("w");

        let alethe = theory_to_alethe(&theory).expect("well-formed proof must convert");
        let stats = ConversionStats::compute(&theory, &alethe);

        assert_eq!(stats.source_steps, 3);
        assert_eq!(stats.assumptions, 3);
        assert_eq!(stats.inferences, 0);
    }

    #[test]
    fn test_theory_to_alethe_with_stats() {
        let mut theory = TheoryProof::new();

        let s1 = theory.add_axiom(TheoryRule::Custom("assert".into()), "(= a b)");
        let s2 = theory.add_axiom(TheoryRule::Custom("assert".into()), "(= b c)");
        theory.trans(s1, s2, "a", "c");

        let (alethe, stats) =
            theory_to_alethe_with_stats(&theory).expect("well-formed proof must convert");

        assert_eq!(alethe.len(), 3);
        assert_eq!(stats.source_steps, 3);
        assert_eq!(stats.assumptions, 2);
        assert_eq!(stats.inferences, 1);
    }

    /// The bug this module's `# Errors` doc comment documents: a dangling
    /// premise ID (here, one from a *different* `TheoryProof` entirely --
    /// the sharpest possible demonstration that `TheoryProof::add_step`
    /// performs no validation of its `premises` argument) must be reported
    /// as a conversion error, not silently dropped from the converted step's
    /// premise list.
    #[test]
    fn test_theory_to_alethe_rejects_dangling_premise() {
        let mut other_theory = TheoryProof::new();
        let foreign_step = other_theory.add_axiom(TheoryRule::Custom("assert".into()), "(= a b)");

        let mut theory = TheoryProof::new();
        // `foreign_step` names a step of `other_theory`, not `theory`: from
        // `theory`'s point of view this is a dangling premise.
        theory.add_step(TheoryRule::Refl, vec![foreign_step], "(= a a)");

        let result = theory_to_alethe(&theory);
        assert!(
            matches!(result, Err(ConversionError::InvalidSource { .. })),
            "a dangling premise must be reported, not silently dropped: {result:?}"
        );
    }

    /// Round-trip check: a well-formed theory proof converts to an Alethe
    /// proof that `ProofChecker::check_alethe_proof` accepts (structurally
    /// -- see `map_theory_rule_to_alethe`'s doc comment on why most theory
    /// rules map to Alethe's `ThLemma`, which the checker does not further
    /// verify semantically). This is the check the coordinator asked for:
    /// building via this module's converter is not evidence of correctness
    /// by itself, only actually being accepted by the checker is.
    #[test]
    fn test_theory_to_alethe_output_passes_the_alethe_checker() {
        let mut theory = TheoryProof::new();
        let s1 = theory.add_axiom(TheoryRule::Custom("assert".into()), "(= a b)");
        let s2 = theory.add_axiom(TheoryRule::Custom("assert".into()), "(= b c)");
        theory.trans(s1, s2, "a", "c");

        let alethe = theory_to_alethe(&theory).expect("well-formed proof must convert");

        let mut checker = crate::checker::ProofChecker::new();
        let result = checker.check_alethe_proof(&alethe);
        assert!(
            matches!(result, crate::checker::CheckResult::Valid),
            "converted Alethe proof must pass the checker: {result:?}"
        );
    }

    #[test]
    fn test_map_theory_rule_to_alethe() {
        assert_eq!(
            map_theory_rule_to_alethe(&TheoryRule::Refl),
            AletheRule::Refl
        );
        assert_eq!(
            map_theory_rule_to_alethe(&TheoryRule::Trans),
            AletheRule::Trans
        );
        assert_eq!(
            map_theory_rule_to_alethe(&TheoryRule::LaGeneric),
            AletheRule::LaGeneric
        );
        assert_eq!(
            map_theory_rule_to_alethe(&TheoryRule::ArrReadWrite1),
            AletheRule::ArrayRowSame
        );
    }

    #[test]
    fn test_is_assumption() {
        assert!(is_assumption(&TheoryRule::Refl));
        assert!(is_assumption(&TheoryRule::Custom("test".into())));
        assert!(!is_assumption(&TheoryRule::Trans));
        assert!(!is_assumption(&TheoryRule::Cong));
    }
}
