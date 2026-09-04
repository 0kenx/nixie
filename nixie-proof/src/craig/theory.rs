//! Theory-specific interpolant generators (LIA, EUF, Array).

use super::parsing::project_to_shared;
use super::partition::Symbol;
use super::term::InterpolantTerm;
use rustc_hash::FxHashSet;

/// Theory-specific interpolant generator
pub trait TheoryInterpolator: Send + Sync {
    /// Theory name
    fn name(&self) -> &'static str;

    /// Check if this theory can handle the given literals
    fn can_handle(&self, literals: &[&str]) -> bool;

    /// Generate theory-specific interpolant
    fn interpolate(
        &self,
        a_literals: &[InterpolantTerm],
        b_literals: &[InterpolantTerm],
        shared_symbols: &FxHashSet<Symbol>,
    ) -> Option<InterpolantTerm>;
}

/// LIA (Linear Integer Arithmetic) interpolator
#[derive(Debug, Default)]
pub struct LiaInterpolator;

impl TheoryInterpolator for LiaInterpolator {
    fn name(&self) -> &'static str {
        "LIA"
    }

    fn can_handle(&self, literals: &[&str]) -> bool {
        literals.iter().any(|l| {
            l.contains('+')
                || l.contains('-')
                || l.contains('*')
                || l.contains("<=")
                || l.contains(">=")
                || l.contains('<')
                || l.contains('>')
        })
    }

    fn interpolate(
        &self,
        a_literals: &[InterpolantTerm],
        b_literals: &[InterpolantTerm],
        shared_symbols: &FxHashSet<Symbol>,
    ) -> Option<InterpolantTerm> {
        // NOTE: this is a sound-but-coarse vocabulary projection, not a full
        // Farkas-lemma certificate; genuine LIA interpolation (computing
        // exact rational coefficients from the theory solver's Farkas
        // combination) is not yet implemented. We only ever expose the
        // shared-vocabulary subset of A's literals, so the vocabulary
        // requirement (the interpolant only mentions symbols common to A and
        // B) is never violated by this fallback.
        if a_literals.is_empty() || b_literals.is_empty() {
            return None;
        }
        Some(project_to_shared(a_literals, shared_symbols))
    }
}

/// EUF (Equality with Uninterpreted Functions) interpolator
#[derive(Debug, Default)]
pub struct EufInterpolator;

impl TheoryInterpolator for EufInterpolator {
    fn name(&self) -> &'static str {
        "EUF"
    }

    fn can_handle(&self, literals: &[&str]) -> bool {
        literals.iter().any(|l| l.contains('=') || l.contains('('))
    }

    fn interpolate(
        &self,
        a_literals: &[InterpolantTerm],
        _b_literals: &[InterpolantTerm],
        shared_symbols: &FxHashSet<Symbol>,
    ) -> Option<InterpolantTerm> {
        // NOTE: sound-but-coarse vocabulary projection; genuine congruence-
        // closure-based interpolation (tracking which equalities are needed
        // to justify each shared-vocabulary consequence) is not yet
        // implemented.
        if a_literals.is_empty() {
            return Some(InterpolantTerm::true_val());
        }
        Some(project_to_shared(a_literals, shared_symbols))
    }
}

/// Array theory interpolator
#[derive(Debug, Default)]
pub struct ArrayInterpolator;

impl TheoryInterpolator for ArrayInterpolator {
    fn name(&self) -> &'static str {
        "Array"
    }

    fn can_handle(&self, literals: &[&str]) -> bool {
        literals
            .iter()
            .any(|l| l.contains("select") || l.contains("store"))
    }

    fn interpolate(
        &self,
        a_literals: &[InterpolantTerm],
        _b_literals: &[InterpolantTerm],
        shared_symbols: &FxHashSet<Symbol>,
    ) -> Option<InterpolantTerm> {
        // NOTE: sound-but-coarse vocabulary projection; genuine array
        // interpolation via read-over-write axiom instantiation is not yet
        // implemented.
        if a_literals.is_empty() {
            return Some(InterpolantTerm::true_val());
        }
        Some(project_to_shared(a_literals, shared_symbols))
    }
}
