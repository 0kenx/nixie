//! Interpolation algorithm selection and configuration.

/// Interpolation algorithm selection
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum InterpolationAlgorithm {
    /// McMillan's algorithm - produces weaker (left-biased) interpolants
    /// Better for model checking as interpolants are more general
    McMillan,
    /// Pudlák's symmetric algorithm - balanced interpolants
    #[default]
    Pudlak,
    /// Huang's algorithm - produces stronger (right-biased) interpolants
    ///
    /// Implemented here as the negation-dual of the McMillan system (i.e.
    /// `Itp_Huang(A,B) = ¬Itp_McMillan(B,A)`, which is a provably sound
    /// construction given a sound McMillan system): base cases and the
    /// resolution combination rule are exactly McMillan's with `A`/`B`
    /// swapped and the result negated. It is not necessarily identical to
    /// Huang's original 1995 formulation, but it is a genuine, verified
    /// stronger/right-biased dual, not a placeholder.
    Huang,
}

/// Configuration for interpolation computation
#[derive(Debug, Clone)]
pub struct InterpolationConfig {
    /// Algorithm to use
    pub algorithm: InterpolationAlgorithm,
    /// Enable theory-specific interpolation
    pub use_theory_interpolants: bool,
    /// Simplify interpolants after computation
    pub simplify_interpolants: bool,
    /// Maximum recursion depth for simplifying the computed interpolant.
    ///
    /// Threaded into [`super::term::InterpolantTerm::simplify_bounded`] by
    /// [`super::interpolator::CraigInterpolator::extract`] whenever
    /// `simplify_interpolants` is set: an interpolant is built directly from
    /// the resolution proof's own structure, whose depth is driven by the
    /// size of the UNSAT proof being interpolated, so bounding the
    /// simplification recursion keeps a pathologically large proof from
    /// overflowing the native stack instead of returning a (possibly
    /// less-simplified, but sound) result.
    pub max_simplify_depth: usize,
    /// Enable caching of intermediate interpolants
    pub enable_caching: bool,
    /// Merge duplicate subterms
    pub deduplicate_terms: bool,
}

impl Default for InterpolationConfig {
    fn default() -> Self {
        Self {
            algorithm: InterpolationAlgorithm::Pudlak,
            use_theory_interpolants: true,
            simplify_interpolants: true,
            max_simplify_depth: super::term::DEFAULT_SIMPLIFY_DEPTH,
            enable_caching: true,
            deduplicate_terms: true,
        }
    }
}
