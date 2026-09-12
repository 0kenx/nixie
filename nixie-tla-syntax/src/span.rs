//! Source positions and spans.
//!
//! Every token and every AST node carries a [`Span`]. This is not optional
//! polish: TLA+ layout is column-sensitive (see [`crate::parser`]), so the
//! parser reads [`Pos::col`] as *grammar input*, not only as diagnostic data.

/// A position in a source file.
///
/// `line` and `col` are 1-based, matching every editor and matching SANY's
/// diagnostics. `offset` is a 0-based byte index into the source text.
///
/// `col` counts **Unicode scalar values**, not bytes, because TLA+ admits the
/// Unicode spellings of its operators (`∧`, `∈`, `⇒`) and a byte-based column
/// would mis-align a junction list that mixes ASCII and Unicode items.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Pos {
    /// 1-based line number.
    pub line: u32,
    /// 1-based column, counted in Unicode scalar values.
    pub col: u32,
    /// 0-based byte offset into the source text.
    pub offset: u32,
}

impl Pos {
    /// The position of the first character of a file.
    pub const START: Self = Self {
        line: 1,
        col: 1,
        offset: 0,
    };

    /// Construct a position.
    #[must_use]
    pub const fn new(line: u32, col: u32, offset: u32) -> Self {
        Self { line, col, offset }
    }
}

impl core::fmt::Display for Pos {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

/// A half-open range of source text, `[start, end)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Span {
    /// First position covered by the span.
    pub start: Pos,
    /// One past the last position covered by the span.
    pub end: Pos,
}

impl Span {
    /// Construct a span from two positions.
    #[must_use]
    pub const fn new(start: Pos, end: Pos) -> Self {
        Self { start, end }
    }

    /// A zero-width span at `pos`.
    #[must_use]
    pub const fn empty(pos: Pos) -> Self {
        Self {
            start: pos,
            end: pos,
        }
    }

    /// The smallest span covering both `self` and `other`.
    #[must_use]
    pub fn merge(self, other: Self) -> Self {
        Self {
            start: if self.start <= other.start {
                self.start
            } else {
                other.start
            },
            end: if self.end.offset >= other.end.offset {
                self.end
            } else {
                other.end
            },
        }
    }

    /// The byte range this span covers, usable to slice the original source.
    #[must_use]
    pub fn byte_range(self) -> core::ops::Range<usize> {
        self.start.offset as usize..self.end.offset as usize
    }
}

impl core::fmt::Display for Span {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.start.line == self.end.line {
            write!(f, "{}:{}-{}", self.start.line, self.start.col, self.end.col)
        } else {
            write!(f, "{}-{}", self.start, self.end)
        }
    }
}
