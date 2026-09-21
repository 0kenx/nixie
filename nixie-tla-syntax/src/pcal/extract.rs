//! Locating a PlusCal algorithm in a TLA+ source file.
//!
//! A PlusCal algorithm is *TLA+ comment text*: `(* --algorithm … *)`. The
//! front end's lexer already scans comments — including nested `(* *)` and
//! `\*` inside them — so extraction is a search over the retained comment
//! list, not a second scanner. The reference translator searches the raw
//! file for `--algorithm` first and `--fair` second; the same order is kept
//! here, restricted to block comments, which is where every corpus algorithm
//! lives and where the grammar puts them. An algorithm outside a comment is
//! an error naming that fact, never a guess.

use crate::error::{ErrorKind, Result, SyntaxError};
use crate::lexer;
use crate::span::Span;
use crate::token::Comment;

/// Where an algorithm was found.
#[derive(Debug, Clone)]
pub struct Found {
    /// The algorithm body: everything from just after the `--algorithm` (or
    /// `--fair`) marker to the end of the enclosing comment. Inner `\*` and
    /// nested `(* *)` comments are still present — the token stream's lexer
    /// treats them exactly as the reference tokenizer does.
    pub body: String,
    /// Whether the marker was `--fair`.
    pub fair: bool,
    /// The span of the whole enclosing comment, delimiters included. The
    /// translation is inserted on the line after it ends.
    pub comment: Span,
}

impl Found {
    /// The line (1-based, in the enclosing file) on which the algorithm
    /// body's first line sits.
    #[must_use]
    pub fn body_start_line(&self) -> u32 {
        self.comment.start.line
    }
}

/// Find the first PlusCal algorithm marker in `src`.
///
/// # Errors
///
/// A [`SyntaxError`] naming the failure: no algorithm, or a marker outside a
/// block comment.
pub fn find_algorithm(src: &str) -> Result<Found> {
    let lexed = lexer::lex(src)?;
    let comments = &lexed.comments;
    // `--algorithm` has priority over `--fair`, matching `PcalParams`.
    let idx = match index_of(comments, "--algorithm").or_else(|| index_of(comments, "--fair")) {
        Some(i) => i,
        None => {
            return Err(SyntaxError::new(
                ErrorKind::Unsupported {
                    construct: "PlusCal translation".into(),
                    note: "no --algorithm or --fair marker found".into(),
                },
                Span::default(),
            ));
        }
    };
    let cmt = &comments[idx];
    if !cmt.block {
        return Err(SyntaxError::new(
            ErrorKind::Unsupported {
                construct: "PlusCal algorithm".into(),
                note: "the marker is not inside a (* *) block comment".into(),
            },
            cmt.span,
        ));
    }
    // The reference searches the whole file for `--algorithm` first, then
    // `--fair`; the same priority, per comment.
    let (off, len, fair) = match (cmt_marker(cmt, "--algorithm"), cmt_marker(cmt, "--fair")) {
        (Some(a), _) => (a, "--algorithm".len(), false),
        (None, Some(f)) => (f, "--fair".len(), true),
        (None, None) => {
            return Err(SyntaxError::new(
                ErrorKind::Unsupported {
                    construct: "PlusCal translation".into(),
                    note: "marker not found in the located comment".into(),
                },
                cmt.span,
            ));
        }
    };
    Ok(Found {
        body: cmt.text[off + len..].to_string(),
        fair,
        comment: cmt.span,
    })
}

fn index_of(comments: &[Comment], marker: &str) -> Option<usize> {
    comments
        .iter()
        .position(|c| cmt_marker(c, marker).is_some())
}

/// The marker's byte offset in the comment, if the comment contains one that
/// is not immediately preceded by a word character.
fn cmt_marker(c: &Comment, marker: &str) -> Option<usize> {
    let mut from = 0;
    while let Some(idx) = c.text[from..].find(marker) {
        let at = from + idx;
        let prev_ok = c.text[..at]
            .chars()
            .next_back()
            .is_none_or(|ch| !(ch.is_alphanumeric() || ch == '_'));
        if prev_ok {
            return Some(at);
        }
        from = at + marker.len();
    }
    None
}
