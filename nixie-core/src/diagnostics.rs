//! Diagnostic System for User-Friendly Error Reporting.
//!
//! Provides rich, colorful error messages with source context,
//! suggestions, and fix-it hints.

use crate::error::{NixieError, SourceSpan};
use crate::error_context::ErrorContext;
#[allow(unused_imports)]
use crate::prelude::*;
use core::fmt;

/// Severity level for diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Severity {
    /// Informational message
    Info,
    /// Warning message
    Warning,
    /// Error message
    Error,
    /// Fatal error (cannot continue)
    Fatal,
}

impl fmt::Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Severity::Info => write!(f, "info"),
            Severity::Warning => write!(f, "warning"),
            Severity::Error => write!(f, "error"),
            Severity::Fatal => write!(f, "fatal"),
        }
    }
}

/// A diagnostic message with source context.
#[derive(Debug, Clone)]
pub struct Diagnostic {
    /// Severity level
    pub severity: Severity,
    /// Main error message
    pub message: String,
    /// Source span where error occurred
    pub span: Option<SourceSpan>,
    /// Additional notes
    pub notes: Vec<String>,
    /// Suggested fixes
    pub fixes: Vec<Fix>,
    /// Related diagnostics
    pub related: Vec<RelatedDiagnostic>,
}

/// A suggested fix for a diagnostic.
#[derive(Debug, Clone)]
pub struct Fix {
    /// Description of the fix
    pub description: String,
    /// Source span to replace
    pub span: SourceSpan,
    /// Replacement text
    pub replacement: String,
}

/// A related diagnostic (for multi-error scenarios).
#[derive(Debug, Clone)]
pub struct RelatedDiagnostic {
    /// Message for this related diagnostic
    pub message: String,
    /// Source span
    pub span: SourceSpan,
}

impl Diagnostic {
    /// Create a new diagnostic.
    pub fn new(severity: Severity, message: impl Into<String>) -> Self {
        Self {
            severity,
            message: message.into(),
            span: None,
            notes: Vec::new(),
            fixes: Vec::new(),
            related: Vec::new(),
        }
    }

    /// Create an error diagnostic.
    pub fn error(message: impl Into<String>) -> Self {
        Self::new(Severity::Error, message)
    }

    /// Create a warning diagnostic.
    pub fn warning(message: impl Into<String>) -> Self {
        Self::new(Severity::Warning, message)
    }

    /// Create an info diagnostic.
    pub fn info(message: impl Into<String>) -> Self {
        Self::new(Severity::Info, message)
    }

    /// Set the source span.
    pub fn with_span(mut self, span: SourceSpan) -> Self {
        self.span = Some(span);
        self
    }

    /// Add a note.
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    /// Add a fix suggestion.
    pub fn with_fix(
        mut self,
        description: impl Into<String>,
        span: SourceSpan,
        replacement: impl Into<String>,
    ) -> Self {
        self.fixes.push(Fix {
            description: description.into(),
            span,
            replacement: replacement.into(),
        });
        self
    }

    /// Add a related diagnostic.
    pub fn with_related(mut self, message: impl Into<String>, span: SourceSpan) -> Self {
        self.related.push(RelatedDiagnostic {
            message: message.into(),
            span,
        });
        self
    }

    /// Format the diagnostic for display.
    pub fn format(&self, source: Option<&str>) -> String {
        let mut output = String::new();

        // Main message
        output.push_str(&format!("{}: {}\n", self.severity, self.message));

        // Source context
        if let Some(span) = &self.span {
            output.push_str(&format!("  --> {}\n", span));

            if let Some(src) = source
                && let Some(context) = self.format_source_context(src, span)
            {
                output.push_str(&context);
            }
        }

        // Notes
        for note in &self.notes {
            output.push_str(&format!("  note: {}\n", note));
        }

        // Fixes
        for fix in &self.fixes {
            output.push_str(&format!("  help: {}\n", fix.description));
            if let Some(src) = source
                && let Some(fix_preview) = self.format_fix_preview(src, fix)
            {
                output.push_str(&fix_preview);
            }
        }

        // Related diagnostics
        for related in &self.related {
            output.push_str(&format!(
                "  related: {} at {}\n",
                related.message, related.span
            ));
        }

        output
    }

    /// Byte offset of the 1-based character column `column` inside `line`.
    ///
    /// Column 0 and column 1 both map to the start of the line, and a column
    /// past the end of the line maps to its end. The result is always a
    /// character boundary, so slicing `line` at it can never panic.
    fn byte_offset_of_column(line: &str, column: usize) -> usize {
        let char_index = column.saturating_sub(1);
        line.char_indices()
            .nth(char_index)
            .map_or(line.len(), |(offset, _)| offset)
    }

    /// Format source context with error highlighting.
    fn format_source_context(&self, source: &str, span: &SourceSpan) -> Option<String> {
        let lines: Vec<&str> = source.lines().collect();

        if span.start.line == 0 || span.start.line > lines.len() {
            return None;
        }

        let mut output = String::new();
        let line_idx = span.start.line - 1;
        let line = lines[line_idx];

        // Line number and source
        output.push_str(&format!("{:4} | {}\n", span.start.line, line));

        // Error marker. Columns are 1-based character positions, so column 0
        // is out of range: clamp it to the start of the line instead of
        // underflowing `column - 1`.
        let start_column = span.start.column.max(1);
        let spaces = start_column - 1;
        let marker_len = if span.start.line == span.end.line {
            span.end.column.saturating_sub(start_column).max(1)
        } else {
            // Character count, not byte length: a multi-byte character is one
            // column, so `line.len()` would over-count the marker.
            line.chars().count().saturating_sub(spaces).max(1)
        };

        output.push_str(&format!(
            "     | {}{}\n",
            " ".repeat(spaces),
            "^".repeat(marker_len)
        ));

        Some(output)
    }

    /// Format fix preview.
    fn format_fix_preview(&self, source: &str, fix: &Fix) -> Option<String> {
        let lines: Vec<&str> = source.lines().collect();

        if fix.span.start.line == 0 || fix.span.start.line > lines.len() {
            return None;
        }

        let line_idx = fix.span.start.line - 1;
        let line = lines[line_idx];

        // Show before and after
        let mut output = String::new();
        output.push_str("     | suggested replacement:\n");

        // Columns are 1-based character positions. Converting them to byte
        // offsets keeps the slices on character boundaries (a byte offset
        // computed from a column would split a multi-byte character and
        // panic), and clamping handles column 0 and an end column that
        // precedes the start column without underflowing.
        let start_column = fix.span.start.column.max(1);
        let before_end = Self::byte_offset_of_column(line, start_column);
        let after_start = if fix.span.start.line == fix.span.end.line {
            Self::byte_offset_of_column(line, fix.span.end.column.max(start_column))
        } else {
            line.len()
        };

        let before = &line[..before_end];
        let after = &line[after_start..];

        output.push_str(&format!("     | {}{}{}\n", before, fix.replacement, after));

        Some(output)
    }
}

/// Convert ErrorContext to Diagnostic.
impl From<ErrorContext> for Diagnostic {
    fn from(ctx: ErrorContext) -> Self {
        let mut diag = match &ctx.error {
            NixieError::ParseErrorWithLocation { location, message } => {
                Diagnostic::error(message).with_span(*location)
            }
            NixieError::SortMismatch {
                location,
                expected,
                found,
            } => Diagnostic::error(format!(
                "type mismatch: expected {}, found {}",
                expected, found
            ))
            .with_span(*location)
            .with_note(format!("expected type: {}", expected))
            .with_note(format!("found type: {}", found)),
            NixieError::UndefinedSymbol { location, symbol } => {
                Diagnostic::error(format!("undefined symbol: {}", symbol))
                    .with_span(*location)
                    .with_note(format!(
                        "consider declaring '{}' with (declare-const {} <type>)",
                        symbol, symbol
                    ))
            }
            NixieError::TypeError { location, message } => {
                Diagnostic::error(message).with_span(*location)
            }
            NixieError::ArityMismatch {
                location,
                expected,
                found,
            } => Diagnostic::error(format!(
                "wrong number of arguments: expected {}, found {}",
                expected, found
            ))
            .with_span(*location),
            _ => Diagnostic::error(ctx.error.to_string()),
        };

        // Add context stack as notes
        for context in ctx.context_stack.iter().rev() {
            diag = diag.with_note(context);
        }

        // Add suggestions as fixes (without specific spans)
        for suggestion in &ctx.suggestions {
            diag.notes.push(format!("help: {}", suggestion));
        }

        diag
    }
}

/// Diagnostic emitter for collecting and displaying diagnostics.
#[derive(Debug, Default)]
pub struct DiagnosticEmitter {
    diagnostics: Vec<Diagnostic>,
    error_count: usize,
    warning_count: usize,
}

impl DiagnosticEmitter {
    /// Create a new diagnostic emitter.
    pub fn new() -> Self {
        Self::default()
    }

    /// Emit a diagnostic.
    pub fn emit(&mut self, diagnostic: Diagnostic) {
        match diagnostic.severity {
            Severity::Error | Severity::Fatal => self.error_count += 1,
            Severity::Warning => self.warning_count += 1,
            Severity::Info => {}
        }
        self.diagnostics.push(diagnostic);
    }

    /// Emit an error diagnostic.
    pub fn error(&mut self, message: impl Into<String>) {
        self.emit(Diagnostic::error(message));
    }

    /// Emit a warning diagnostic.
    pub fn warning(&mut self, message: impl Into<String>) {
        self.emit(Diagnostic::warning(message));
    }

    /// Emit an info diagnostic.
    pub fn info(&mut self, message: impl Into<String>) {
        self.emit(Diagnostic::info(message));
    }

    /// Check if there are any errors.
    pub fn has_errors(&self) -> bool {
        self.error_count > 0
    }

    /// Get error count.
    pub fn error_count(&self) -> usize {
        self.error_count
    }

    /// Get warning count.
    pub fn warning_count(&self) -> usize {
        self.warning_count
    }

    /// Get all diagnostics.
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    /// Format all diagnostics.
    pub fn format_all(&self, source: Option<&str>) -> String {
        let mut output = String::new();

        for diag in &self.diagnostics {
            output.push_str(&diag.format(source));
            output.push('\n');
        }

        // Summary
        if self.error_count > 0 || self.warning_count > 0 {
            output.push_str(&format!(
                "{} error(s), {} warning(s)\n",
                self.error_count, self.warning_count
            ));
        }

        output
    }

    /// Clear all diagnostics.
    pub fn clear(&mut self) {
        self.diagnostics.clear();
        self.error_count = 0;
        self.warning_count = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::{SourceLocation, SourceSpan};

    #[test]
    fn test_diagnostic_creation() {
        let diag = Diagnostic::error("test error");
        assert_eq!(diag.severity, Severity::Error);
        assert_eq!(diag.message, "test error");
    }

    #[test]
    fn test_diagnostic_with_note() {
        let diag = Diagnostic::error("test").with_note("additional info");
        assert_eq!(diag.notes.len(), 1);
        assert_eq!(diag.notes[0], "additional info");
    }

    #[test]
    fn test_diagnostic_emitter() {
        let mut emitter = DiagnosticEmitter::new();

        emitter.error("error 1");
        emitter.warning("warning 1");
        emitter.info("info 1");

        assert_eq!(emitter.error_count(), 1);
        assert_eq!(emitter.warning_count(), 1);
        assert!(emitter.has_errors());
    }

    #[test]
    fn test_severity_ordering() {
        assert!(Severity::Info < Severity::Warning);
        assert!(Severity::Warning < Severity::Error);
        assert!(Severity::Error < Severity::Fatal);
    }

    #[test]
    fn test_diagnostic_format() {
        let loc = SourceLocation::new(1, 5, 4);
        let span = SourceSpan::from_location(loc);

        let diag = Diagnostic::error("unexpected token")
            .with_span(span)
            .with_note("expected ')'");

        let formatted = diag.format(Some("(foo bar"));
        assert!(formatted.contains("error"));
        assert!(formatted.contains("unexpected token"));
        assert!(formatted.contains("note"));
    }

    /// Build a diagnostic carrying a single fix over the given span.
    fn diagnostic_with_fix(span: SourceSpan, replacement: &str) -> Diagnostic {
        Diagnostic::error("boom").with_fix("try this", span, replacement)
    }

    #[test]
    fn test_fix_preview_column_zero_does_not_underflow() {
        // Column 0 is out of range for a 1-based column; `column - 1` used to
        // underflow to `usize::MAX` and then slice out of bounds.
        let span = SourceSpan::new(SourceLocation::new(1, 0, 0), SourceLocation::new(1, 0, 0));
        let formatted = diagnostic_with_fix(span, "X").format(Some("abc"));
        assert!(formatted.contains("suggested replacement"));
        assert!(formatted.contains("Xabc"));
    }

    #[test]
    fn test_fix_preview_end_before_start_does_not_underflow() {
        // A malformed span whose end precedes its start: the replacement is
        // simply inserted, never an arithmetic underflow.
        let span = SourceSpan::new(SourceLocation::new(1, 3, 2), SourceLocation::new(1, 1, 0));
        let formatted = diagnostic_with_fix(span, "X").format(Some("abcdef"));
        assert!(formatted.contains("abXcdef"));
    }

    #[test]
    fn test_fix_preview_beyond_line_end_is_clamped() {
        let span = SourceSpan::new(
            SourceLocation::new(1, 99, 98),
            SourceLocation::new(1, 120, 119),
        );
        let formatted = diagnostic_with_fix(span, "X").format(Some("abc"));
        assert!(formatted.contains("abcX"));
    }

    #[test]
    fn test_fix_preview_respects_char_boundaries() {
        // Every character here is multi-byte, so a byte-indexed slice at
        // column 2 would land inside a character and panic.
        let span = SourceSpan::new(SourceLocation::new(1, 2, 3), SourceLocation::new(1, 3, 6));
        let formatted = diagnostic_with_fix(span, "X").format(Some("日本語"));
        assert!(formatted.contains("日X語"), "got: {formatted}");
    }

    #[test]
    fn test_source_context_column_zero_does_not_underflow() {
        // Multi-line span starting at column 0: the marker length used to be
        // `line.len() - (column - 1)`, an underflow on both operands.
        let span = SourceSpan::new(SourceLocation::new(1, 0, 0), SourceLocation::new(2, 1, 5));
        let formatted = Diagnostic::error("boom")
            .with_span(span)
            .format(Some("abc\ndef"));
        assert!(formatted.contains("^^^"));
    }

    #[test]
    fn test_source_context_multiline_marker_counts_characters() {
        let span = SourceSpan::new(SourceLocation::new(1, 2, 3), SourceLocation::new(2, 1, 20));
        let formatted = Diagnostic::error("boom")
            .with_span(span)
            .format(Some("日本語\nx"));
        // Two remaining characters, not the six remaining bytes. One leading
        // space places the marker under the second character.
        assert!(formatted.contains("|  ^^\n"), "got: {formatted}");
    }
}
