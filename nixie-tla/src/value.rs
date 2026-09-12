//! TLA+ values, and printing them the way TLC does.
//!
//! The point of having values at all is **semantic** validation. Everything
//! the front end has been checked against so far — SANY parity, level parity,
//! lowering coverage — is structural. None of it would have caught the
//! `INSTANCE` visibility bug, which produced a perfectly well-formed kernel
//! term that read the wrong module's variables.
//!
//! Evaluating a lowered term and comparing the result against TLC's is the
//! check that closes that gap, and the printed form here is chosen to match
//! TLC's output so the comparison can be textual.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// A TLA+ value.
///
/// Ordered so that sets can be [`BTreeSet`]s. The order across variants is
/// arbitrary but total and stable, which is all a set needs; it is **not** the
/// TLA+ `<` relation and must not be used as one.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Value {
    /// `TRUE` / `FALSE`.
    Bool(bool),
    /// An integer.
    ///
    /// `i128` rather than `i64`: TLA+ integers are unbounded, and this
    /// codebase has been bitten by silent truncation before. Arithmetic that
    /// would overflow raises an error instead of wrapping.
    Int(i128),
    /// A string.
    Str(String),
    /// A set.
    Set(BTreeSet<Value>),
    /// A tuple, which in TLA+ is a function on `1..n`.
    Tuple(Vec<Value>),
    /// A record, which is a function on a set of field-name strings.
    Record(BTreeMap<String, Value>),
    /// A finite function.
    Fun(BTreeMap<Value, Value>),
}

impl Value {
    /// The set of values, built from an iterator.
    pub fn set<I: IntoIterator<Item = Value>>(items: I) -> Self {
        Self::Set(items.into_iter().collect())
    }

    /// Whether this is `TRUE`.
    #[must_use]
    pub fn is_true(&self) -> bool {
        matches!(self, Self::Bool(true))
    }

    /// A short name for the kind, for diagnostics.
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::Bool(_) => "a boolean",
            Self::Int(_) => "an integer",
            Self::Str(_) => "a string",
            Self::Set(_) => "a set",
            Self::Tuple(_) => "a tuple",
            Self::Record(_) => "a record",
            Self::Fun(_) => "a function",
        }
    }
}

impl fmt::Display for Value {
    /// Print as TLC does, so that a differential comparison can be textual.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool(b) => f.write_str(if *b { "TRUE" } else { "FALSE" }),
            Self::Int(i) => write!(f, "{i}"),
            Self::Str(s) => write!(f, "{s:?}"),
            Self::Set(xs) => {
                f.write_str("{")?;
                for (i, x) in xs.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{x}")?;
                }
                f.write_str("}")
            }
            Self::Tuple(xs) => {
                f.write_str("<<")?;
                for (i, x) in xs.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{x}")?;
                }
                f.write_str(">>")
            }
            Self::Record(fs) => {
                f.write_str("[")?;
                for (i, (k, v)) in fs.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{k} |-> {v}")?;
                }
                f.write_str("]")
            }
            // TLC prints a function as `(k1 :> v1 @@ k2 :> v2)`.
            Self::Fun(m) => {
                if m.is_empty() {
                    return f.write_str("<<>>");
                }
                f.write_str("(")?;
                for (i, (k, v)) in m.iter().enumerate() {
                    if i > 0 {
                        f.write_str(" @@ ")?;
                    }
                    write!(f, "{k} :> {v}")?;
                }
                f.write_str(")")
            }
        }
    }
}
