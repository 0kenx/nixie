//! Lowering diagnostics.

use nixie_tla_syntax::Span;
use thiserror::Error;

/// Why an expression could not be lowered to the kernel.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum LowerErrorKind {
    /// A construct that is real TLA+ but has no kernel form.
    ///
    /// Never silently dropped: `AGENTS.md` requires unhandled input to raise
    /// an error rather than take a default, and a model checker that quietly
    /// ignores a conjunct is exactly how a wrong `sat` ships.
    #[error("{construct} has no kernel form: {note}")]
    Unsupported {
        /// The construct that was found.
        construct: String,
        /// Why, and what to do instead.
        note: String,
    },

    /// An operator was applied to the wrong number of arguments.
    #[error("`{name}` takes {expected} argument(s) but was given {found}")]
    Arity {
        /// The operator.
        name: String,
        /// How many it was defined with.
        expected: usize,
        /// How many it was applied to.
        found: usize,
    },

    /// Inlining did not terminate within the configured budget.
    ///
    /// Almost always a recursive operator: TLA+ allows `RECURSIVE`, and
    /// unfolding it has no fixed point. Returned rather than looping.
    #[error("inlining exceeded the depth limit of {limit}, expanding `{name}`")]
    InlineLimit {
        /// The operator being expanded when the limit was hit.
        name: String,
        /// The configured limit.
        limit: usize,
    },

    /// Expression nesting beyond the configured limit.
    #[error("expression nests deeper than the limit of {limit}")]
    DepthLimit {
        /// The configured limit.
        limit: usize,
    },
}

/// A located lowering error.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[error("{span}: {kind}")]
pub struct LowerError {
    /// What went wrong.
    pub kind: LowerErrorKind,
    /// Where it went wrong.
    pub span: Span,
}

impl LowerError {
    /// Construct a located error.
    #[must_use]
    pub fn new(kind: LowerErrorKind, span: Span) -> Self {
        Self { kind, span }
    }

    /// An `Unsupported` error.
    #[must_use]
    pub fn unsupported(construct: &str, note: &str, span: Span) -> Self {
        Self::new(
            LowerErrorKind::Unsupported {
                construct: construct.to_string(),
                note: note.to_string(),
            },
            span,
        )
    }
}

/// Result alias for lowering.
pub type Result<T> = core::result::Result<T, LowerError>;
