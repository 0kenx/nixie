//! Textual clause parsing helpers.
//!
// This crate's proof steps carry conclusions as opaque strings rather than
// structured terms, so there is no general SMT-LIB term parser available
// here. The helpers below understand exactly the minimal clause syntax this
// module itself relies on: a bare atom, `(not X)`, and `(or L1 L2 ... Ln)`.
// Anything else is treated as a single opaque atomic literal (its exact text
// becomes the literal's symbol name) -- honest best-effort, never fabricated
// structure.

use super::partition::Symbol;
use super::term::InterpolantTerm;
use rustc_hash::FxHashSet;

/// Parse a textual clause conclusion into its literals.
pub(crate) fn parse_clause_literals(conclusion: &str) -> Vec<InterpolantTerm> {
    let trimmed = conclusion.trim();
    if let Some(inner) = strip_wrapped(trimmed, "or") {
        split_top_level(inner)
            .into_iter()
            .map(parse_literal)
            .collect()
    } else {
        vec![parse_literal(trimmed)]
    }
}

/// Parse a single literal: `(not X)` becomes `¬parse(X)`; `true`/`false`
/// become the corresponding constants; anything else becomes an opaque
/// atomic variable named after its exact text.
///
/// Iterative: `(not (not (not ...)))` in an untrusted conclusion string cost one
/// call frame per `not`, and `-> InterpolantTerm` offers no channel through
/// which a depth cap could report truncation. Peeling the `not` wrappers in a
/// loop and re-applying [`InterpolantTerm::not`] the same number of times is
/// exactly equivalent, including its double-negation and constant collapsing.
fn parse_literal(text: &str) -> InterpolantTerm {
    let mut trimmed = text.trim();
    let mut negations = 0usize;

    while let Some(inner) = strip_wrapped(trimmed, "not") {
        negations += 1;
        trimmed = inner.trim();
    }

    let mut term = match trimmed {
        "true" => InterpolantTerm::true_val(),
        "false" => InterpolantTerm::false_val(),
        _ => InterpolantTerm::var(trimmed),
    };
    for _ in 0..negations {
        term = InterpolantTerm::not(term);
    }
    term
}

/// If `text` is `(keyword ...)`, return the content following `keyword`.
fn strip_wrapped<'a>(text: &'a str, keyword: &str) -> Option<&'a str> {
    let inner = text.strip_prefix('(')?.strip_suffix(')')?;
    let inner = inner.trim();
    let rest = inner.strip_prefix(keyword)?;
    if rest.is_empty() {
        Some(rest)
    } else if rest.starts_with(char::is_whitespace) {
        Some(rest.trim_start())
    } else {
        None
    }
}

/// Split `text` on top-level whitespace, treating parenthesised groups as
/// atomic (so `(f x y) z` splits into `["(f x y)", "z"]`).
fn split_top_level(text: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut start: Option<usize> = None;

    for (i, ch) in text.char_indices() {
        match ch {
            '(' => {
                depth += 1;
                start.get_or_insert(i);
            }
            ')' => {
                depth -= 1;
            }
            c if c.is_whitespace() && depth == 0 => {
                if let Some(s) = start.take() {
                    out.push(&text[s..i]);
                }
            }
            _ => {
                start.get_or_insert(i);
            }
        }
    }
    if let Some(s) = start {
        out.push(&text[s..]);
    }
    out
}

/// Classification of a symbol relative to the known A/B vocabulary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PivotLocality {
    /// Known to occur only on the A side.
    ALocal,
    /// Known to occur only on the B side.
    BLocal,
    /// Occurs on both sides (or was explicitly declared shared).
    Global,
}

/// A detected resolution pivot between two premise clauses.
#[derive(Debug, Clone)]
pub(crate) struct ResolutionPivot {
    /// Index (0 or 1) of the premise holding the *positive* pivot literal.
    pub(crate) positive_index: usize,
    /// The pivot's underlying symbol.
    pub(crate) symbol: Symbol,
}

/// Find the unique resolution pivot between two clauses given as raw text.
///
/// Returns `None` (rather than guessing) when the clauses cannot be parsed
/// into literal sets, or when there is not *exactly one* complementary
/// literal pair between them -- an ambiguous or absent pivot must not be
/// fabricated.
pub(crate) fn find_resolution_pivot(clause_a: &str, clause_b: &str) -> Option<ResolutionPivot> {
    let lits_a = parse_clause_literals(clause_a);
    let lits_b = parse_clause_literals(clause_b);

    let mut found: Option<ResolutionPivot> = None;
    for la in &lits_a {
        for lb in &lits_b {
            if let Some(pivot) = pivot_from_pair(la, lb) {
                if found.is_some() {
                    return None;
                }
                found = Some(pivot);
            }
        }
    }
    found
}

/// If `a_lit` and `b_lit` are complementary atomic literals, return the pivot
/// with `positive_index` indicating which side holds the positive occurrence.
fn pivot_from_pair(a_lit: &InterpolantTerm, b_lit: &InterpolantTerm) -> Option<ResolutionPivot> {
    match (a_lit, b_lit) {
        (InterpolantTerm::Not(inner), other) if inner.as_ref() == other => {
            let mut symbols = FxHashSet::default();
            other.collect_symbols(&mut symbols);
            Some(ResolutionPivot {
                positive_index: 1,
                symbol: single_symbol(&symbols)?,
            })
        }
        (other, InterpolantTerm::Not(inner)) if inner.as_ref() == other => {
            let mut symbols = FxHashSet::default();
            other.collect_symbols(&mut symbols);
            Some(ResolutionPivot {
                positive_index: 0,
                symbol: single_symbol(&symbols)?,
            })
        }
        _ => None,
    }
}

fn single_symbol(symbols: &FxHashSet<Symbol>) -> Option<Symbol> {
    if symbols.len() == 1 {
        symbols.iter().next().cloned()
    } else {
        None
    }
}

/// Detect the resolution pivot for a binary resolution inference step, or
/// `None` if this is not a two-premise `"resolution"` step or the pivot could
/// not be recovered from the textual clause representation.
pub(crate) fn resolution_pivot(
    rule: &str,
    premise_interpolants: &[InterpolantTerm],
    premise_conclusions: &[&str],
) -> Option<ResolutionPivot> {
    if rule != "resolution" || premise_interpolants.len() != 2 || premise_conclusions.len() != 2 {
        return None;
    }
    find_resolution_pivot(premise_conclusions[0], premise_conclusions[1])
}

/// Project a set of literals down to the conjunction of those entirely within
/// `shared_symbols`; literals mentioning any non-shared symbol are dropped
/// rather than leaked into the result. An empty projection yields `true` (a
/// sound, if maximally coarse, contribution).
pub(crate) fn project_to_shared(
    literals: &[InterpolantTerm],
    shared_symbols: &FxHashSet<Symbol>,
) -> InterpolantTerm {
    let projected: Vec<InterpolantTerm> = literals
        .iter()
        .filter(|lit| {
            let mut symbols = FxHashSet::default();
            lit.collect_symbols(&mut symbols);
            !symbols.is_empty() && symbols.iter().all(|s| shared_symbols.contains(s))
        })
        .cloned()
        .collect();
    if projected.is_empty() {
        InterpolantTerm::true_val()
    } else {
        InterpolantTerm::and(projected)
    }
}
