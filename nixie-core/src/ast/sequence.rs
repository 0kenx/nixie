//! Native generic finite-sequence language, using CVC5's zero-based semantics.
use super::{TermId, TermKind, TermManager};
use crate::error::{NixieError, Result};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::sort::{SortId, SortKind};

/// Sequence operators. Empty carries its complete sequence sort.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SeqOp {
    /// Empty sequence.
    Empty(SortId),
    /// Singleton.
    Unit,
    /// Concatenation.
    Concat,
    /// Length.
    Len,
    /// Element at a zero-based index; unspecified outside the domain.
    Nth,
    /// Clipped extraction; invalid starts or nonpositive sizes yield empty.
    Extract,
    /// Length-preserving replacement, clipped at the end.
    Update,
}
impl SeqOp {
    /// SMT-LIB operator spelling.
    pub fn name(self) -> &'static str {
        match self {
            Self::Empty(_) => "seq.empty",
            Self::Unit => "seq.unit",
            Self::Concat => "seq.++",
            Self::Len => "seq.len",
            Self::Nth => "seq.nth",
            Self::Extract => "seq.extract",
            Self::Update => "seq.update",
        }
    }
    /// Parse an unqualified operator (empty needs a sort qualification).
    pub fn from_name(name: &str) -> Option<Self> {
        Some(match name {
            "seq.unit" => Self::Unit,
            "seq.++" => Self::Concat,
            "seq.len" => Self::Len,
            "seq.nth" => Self::Nth,
            "seq.extract" => Self::Extract,
            "seq.update" => Self::Update,
            _ => return None,
        })
    }
}
impl TermManager {
    /// Build a native sequence operator with full arity and sort checking.
    ///
    /// # Errors
    /// Rejects missing terms, incorrect arities, and inconsistent sorts.
    pub fn mk_sequence(&mut self, op: SeqOp, args: &[TermId]) -> Result<TermId> {
        if let (SeqOp::Unit, [a]) = (op, args)
            && let Some(t) = self.get(*a)
        {
            self.sorts.seq(t.sort);
        }
        let sort = infer_sequence_sort(self, op, args)?;
        Ok(self.intern_term(TermKind::Sequence(op, args.iter().copied().collect()), sort))
    }
}

/// Infer and validate a native sequence operator's sort without trusting its result annotation.
///
/// # Errors
/// Rejects incorrect arities, missing sorts/operands, and mismatched operand sorts.
pub fn infer_sequence_sort(manager: &TermManager, op: SeqOp, args: &[TermId]) -> Result<SortId> {
    let err = || NixieError::ParseError {
        position: 0,
        message: format!("ill-sorted or wrong arity for {}", op.name()),
    };
    let sorts: Vec<SortId> = args
        .iter()
        .map(|a| manager.get(*a).map(|t| t.sort).ok_or_else(err))
        .collect::<Result<_>>()?;
    if sorts.iter().any(|s| manager.sorts.get(*s).is_none()) {
        return Err(err());
    }
    let sort = match (op, sorts.as_slice()) {
        (SeqOp::Empty(s), [])
            if matches!(
                manager.sorts.get(s).map(|s| &s.kind),
                Some(SortKind::Seq(_))
            ) =>
        {
            s
        }
        (SeqOp::Unit, [e]) => manager.sorts.find(&SortKind::Seq(*e)).ok_or_else(err)?,
        (SeqOp::Concat, [s, ..])
            if sorts.iter().all(|t| t == s)
                && matches!(
                    manager.sorts.get(*s).map(|s| &s.kind),
                    Some(SortKind::Seq(_))
                ) =>
        {
            *s
        }
        (SeqOp::Len, [s]) => {
            if !matches!(
                manager.sorts.get(*s).map(|s| &s.kind),
                Some(SortKind::Seq(_))
            ) {
                return Err(err());
            }
            manager.sorts.int_sort
        }
        (SeqOp::Nth, [s, i]) if *i == manager.sorts.int_sort => {
            let Some(SortKind::Seq(e)) = manager.sorts.get(*s).map(|s| &s.kind) else {
                return Err(err());
            };
            *e
        }
        (SeqOp::Extract, [s, i, n])
            if *i == manager.sorts.int_sort && *n == manager.sorts.int_sort =>
        {
            if !matches!(
                manager.sorts.get(*s).map(|s| &s.kind),
                Some(SortKind::Seq(_))
            ) {
                return Err(err());
            }
            *s
        }
        (SeqOp::Update, [s, i, t]) if *i == manager.sorts.int_sort && s == t => {
            if !matches!(
                manager.sorts.get(*s).map(|s| &s.kind),
                Some(SortKind::Seq(_))
            ) {
                return Err(err());
            }
            *s
        }
        _ => return Err(err()),
    };
    Ok(sort)
}

/// Print sequence spines on a heap stack, including nested sequence elements.
pub fn print_sequence(root: TermId, manager: &TermManager) -> String {
    use core::fmt::Write;
    enum Step {
        Term(TermId),
        Text(&'static str),
    }
    let mut stack = vec![Step::Term(root)];
    let mut out = String::new();
    let printer = crate::smtlib::Printer::new(manager);
    while let Some(step) = stack.pop() {
        match step {
            Step::Text(s) => out.push_str(s),
            Step::Term(id) => match manager.get(id).map(|t| &t.kind) {
                Some(TermKind::Sequence(SeqOp::Empty(sort), _)) => {
                    out.push_str("(as seq.empty ");
                    printer.write_sort(&mut out, *sort);
                    out.push(')');
                }
                Some(TermKind::Sequence(op, args)) => {
                    let _ = write!(out, "({}", op.name());
                    stack.push(Step::Text(")"));
                    for &a in args.iter().rev() {
                        stack.push(Step::Term(a));
                        stack.push(Step::Text(" "));
                    }
                }
                _ => printer.write_term(&mut out, id),
            },
        }
    }
    out
}
