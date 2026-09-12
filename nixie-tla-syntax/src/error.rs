//! Syntax diagnostics.
//!
//! Every error carries a [`Span`]. Nothing in this crate reports a failure
//! without saying where it happened: this is the user-facing surface of the
//! whole TLA+ pipeline, and a parser that cannot point at the offending token
//! is not usable as a SANY replacement.

use crate::span::Span;
use thiserror::Error;

/// What went wrong.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum ErrorKind {
    /// A character that cannot begin any TLA+ lexeme.
    #[error("unexpected character {0:?}")]
    UnexpectedChar(char),

    /// A `"` string literal ran to end of file or end of line.
    #[error("unterminated string literal")]
    UnterminatedString,

    /// A `(*` block comment ran to end of file.
    #[error("unterminated block comment")]
    UnterminatedComment,

    /// A `\` escape inside a string that TLA+ does not define.
    #[error("unknown string escape `\\{0}`")]
    InvalidEscape(char),

    /// A based numeral prefix with no digits after it, e.g. a bare `\h`.
    #[error("numeral prefix `{0}` with no digits")]
    EmptyNumeral(String),

    /// A `\`-word that is not in the (closed) TLA+ operator table.
    #[error("`{0}` is not a TLA+ operator")]
    UnknownOperator(String),

    /// The parser wanted something else here.
    #[error("expected {expected}, found {found}")]
    Unexpected {
        /// What the grammar allowed at this point.
        expected: String,
        /// What was actually there.
        found: String,
    },

    /// Two adjacent operators whose precedence intervals overlap.
    ///
    /// This is the diagnostic that motivates the Pratt parser: an LR encoding
    /// of TLA+ precedence cannot distinguish this case from a generic parse
    /// failure. See `docs/TLA_FRONTEND_DESIGN.md` §1.0.
    #[error(
        "`{left}` ({left_lo}-{left_hi}) and `{right}` ({right_lo}-{right_hi}) have overlapping precedence; parenthesise to disambiguate"
    )]
    PrecedenceConflict {
        /// Canonical spelling of the operator already applied.
        left: String,
        /// Low end of the left operator's interval.
        left_lo: u8,
        /// High end of the left operator's interval.
        left_hi: u8,
        /// Canonical spelling of the operator that cannot follow it.
        right: String,
        /// Low end of the right operator's interval.
        right_lo: u8,
        /// High end of the right operator's interval.
        right_hi: u8,
    },

    /// A junction-list item that does not line up with the list it belongs to.
    #[error(
        "junction list item starts at column {found}, but the list is aligned at column {expected}"
    )]
    JunctionMisaligned {
        /// Column the enclosing list is aligned at.
        expected: u32,
        /// Column this item was written at.
        found: u32,
    },

    /// Nesting deeper than the configured limit.
    ///
    /// Returned rather than overflowing the stack. `AGENTS.md` forbids
    /// unbounded native recursion over user-controlled input; a hand-written
    /// recursive-descent parser is recursion over user-controlled input, so
    /// the depth is bounded explicitly and the limit is a diagnostic.
    #[error("expression nests deeper than the limit of {limit}")]
    RecursionLimit {
        /// The configured maximum depth.
        limit: usize,
    },

    /// A construct that is real TLA+ but outside the milestone-1 fragment.
    ///
    /// Never silently ignored. `AGENTS.md`: unhandled input raises an error,
    /// it does not get a default.
    #[error("{construct} is not supported: {note}")]
    Unsupported {
        /// The construct that was found.
        construct: String,
        /// Why it is not supported, and what to do instead.
        note: String,
    },
}

/// A syntax error, located in the source.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[error("{span}: {kind}")]
pub struct SyntaxError {
    /// What went wrong.
    pub kind: ErrorKind,
    /// Where it went wrong.
    pub span: Span,
}

impl SyntaxError {
    /// Construct a located error.
    #[must_use]
    pub fn new(kind: ErrorKind, span: Span) -> Self {
        Self { kind, span }
    }
}

/// Result alias for this crate.
pub type Result<T> = core::result::Result<T, SyntaxError>;
