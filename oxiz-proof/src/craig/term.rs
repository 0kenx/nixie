//! Interpolant term representation.

use super::partition::Symbol;
use num_rational::BigRational;
use rustc_hash::FxHashSet;
use std::fmt;

/// An interpolant formula in a simple term representation
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InterpolantTerm {
    /// Boolean constant
    Bool(bool),
    /// Variable
    Var(Symbol),
    /// Negation
    Not(Box<InterpolantTerm>),
    /// Conjunction
    And(Vec<InterpolantTerm>),
    /// Disjunction
    Or(Vec<InterpolantTerm>),
    /// Implication
    Implies(Box<InterpolantTerm>, Box<InterpolantTerm>),
    /// Equality
    Eq(Box<InterpolantTerm>, Box<InterpolantTerm>),
    /// Less than
    Lt(Box<InterpolantTerm>, Box<InterpolantTerm>),
    /// Less than or equal
    Le(Box<InterpolantTerm>, Box<InterpolantTerm>),
    /// Integer/Rational constant
    Num(BigRational),
    /// Addition
    Add(Vec<InterpolantTerm>),
    /// Subtraction
    Sub(Box<InterpolantTerm>, Box<InterpolantTerm>),
    /// Multiplication
    Mul(Vec<InterpolantTerm>),
    /// Function application
    App(Symbol, Vec<InterpolantTerm>),
    /// Array select
    Select(Box<InterpolantTerm>, Box<InterpolantTerm>),
    /// Array store
    Store(
        Box<InterpolantTerm>,
        Box<InterpolantTerm>,
        Box<InterpolantTerm>,
    ),
}

impl InterpolantTerm {
    /// Create true
    #[must_use]
    pub fn true_val() -> Self {
        Self::Bool(true)
    }

    /// Create false
    #[must_use]
    pub fn false_val() -> Self {
        Self::Bool(false)
    }

    /// Create a variable
    #[must_use]
    pub fn var(name: impl Into<String>) -> Self {
        Self::Var(Symbol::var(name))
    }

    /// Create a negation
    #[must_use]
    #[allow(clippy::should_implement_trait)]
    pub fn not(term: Self) -> Self {
        match term {
            Self::Bool(b) => Self::Bool(!b),
            Self::Not(inner) => *inner,
            _ => Self::Not(Box::new(term)),
        }
    }

    /// Create a conjunction
    #[must_use]
    pub fn and(terms: Vec<Self>) -> Self {
        let mut flat = Vec::new();
        for t in terms {
            match t {
                Self::Bool(true) => continue,
                Self::Bool(false) => return Self::Bool(false),
                Self::And(inner) => flat.extend(inner),
                other => flat.push(other),
            }
        }
        if flat.is_empty() {
            Self::Bool(true)
        } else if flat.len() == 1 {
            flat.pop().unwrap_or(Self::Bool(true))
        } else {
            Self::And(flat)
        }
    }

    /// Create a disjunction
    #[must_use]
    pub fn or(terms: Vec<Self>) -> Self {
        let mut flat = Vec::new();
        for t in terms {
            match t {
                Self::Bool(false) => continue,
                Self::Bool(true) => return Self::Bool(true),
                Self::Or(inner) => flat.extend(inner),
                other => flat.push(other),
            }
        }
        if flat.is_empty() {
            Self::Bool(false)
        } else if flat.len() == 1 {
            flat.pop().unwrap_or(Self::Bool(false))
        } else {
            Self::Or(flat)
        }
    }

    /// Create an implication
    #[must_use]
    pub fn implies(lhs: Self, rhs: Self) -> Self {
        match (&lhs, &rhs) {
            (Self::Bool(false), _) => Self::Bool(true),
            (Self::Bool(true), _) => rhs,
            (_, Self::Bool(true)) => Self::Bool(true),
            (_, Self::Bool(false)) => Self::not(lhs),
            _ => Self::Implies(Box::new(lhs), Box::new(rhs)),
        }
    }

    /// Check if this term is true
    #[must_use]
    pub fn is_true(&self) -> bool {
        matches!(self, Self::Bool(true))
    }

    /// Check if this term is false
    #[must_use]
    pub fn is_false(&self) -> bool {
        matches!(self, Self::Bool(false))
    }

    /// Collect all symbols in the term
    pub fn collect_symbols(&self, symbols: &mut FxHashSet<Symbol>) {
        match self {
            Self::Bool(_) | Self::Num(_) => {}
            Self::Var(s) => {
                symbols.insert(s.clone());
            }
            Self::Not(t) => t.collect_symbols(symbols),
            Self::And(ts) | Self::Or(ts) | Self::Add(ts) | Self::Mul(ts) => {
                for t in ts {
                    t.collect_symbols(symbols);
                }
            }
            Self::Implies(a, b)
            | Self::Eq(a, b)
            | Self::Lt(a, b)
            | Self::Le(a, b)
            | Self::Sub(a, b)
            | Self::Select(a, b) => {
                a.collect_symbols(symbols);
                b.collect_symbols(symbols);
            }
            Self::App(f, args) => {
                symbols.insert(f.clone());
                for arg in args {
                    arg.collect_symbols(symbols);
                }
            }
            Self::Store(a, i, v) => {
                a.collect_symbols(symbols);
                i.collect_symbols(symbols);
                v.collect_symbols(symbols);
            }
        }
    }

    /// Simplify the term
    #[must_use]
    pub fn simplify(&self) -> Self {
        match self {
            Self::Bool(_) | Self::Num(_) | Self::Var(_) => self.clone(),
            Self::Not(t) => Self::not(t.simplify()),
            Self::And(ts) => Self::and(ts.iter().map(|t| t.simplify()).collect()),
            Self::Or(ts) => Self::or(ts.iter().map(|t| t.simplify()).collect()),
            Self::Implies(a, b) => Self::implies(a.simplify(), b.simplify()),
            Self::Eq(a, b) => {
                let sa = a.simplify();
                let sb = b.simplify();
                if sa == sb {
                    Self::Bool(true)
                } else {
                    Self::Eq(Box::new(sa), Box::new(sb))
                }
            }
            _ => self.clone(),
        }
    }
}

impl fmt::Display for InterpolantTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool(b) => write!(f, "{}", b),
            Self::Var(s) => write!(f, "{}", s.name),
            Self::Not(t) => write!(f, "(not {})", t),
            Self::And(ts) => {
                write!(f, "(and")?;
                for t in ts {
                    write!(f, " {}", t)?;
                }
                write!(f, ")")
            }
            Self::Or(ts) => {
                write!(f, "(or")?;
                for t in ts {
                    write!(f, " {}", t)?;
                }
                write!(f, ")")
            }
            Self::Implies(a, b) => write!(f, "(=> {} {})", a, b),
            Self::Eq(a, b) => write!(f, "(= {} {})", a, b),
            Self::Lt(a, b) => write!(f, "(< {} {})", a, b),
            Self::Le(a, b) => write!(f, "(<= {} {})", a, b),
            Self::Num(n) => write!(f, "{}", n),
            Self::Add(ts) => {
                write!(f, "(+")?;
                for t in ts {
                    write!(f, " {}", t)?;
                }
                write!(f, ")")
            }
            Self::Sub(a, b) => write!(f, "(- {} {})", a, b),
            Self::Mul(ts) => {
                write!(f, "(*")?;
                for t in ts {
                    write!(f, " {}", t)?;
                }
                write!(f, ")")
            }
            Self::App(s, args) => {
                write!(f, "({}", s.name)?;
                for arg in args {
                    write!(f, " {}", arg)?;
                }
                write!(f, ")")
            }
            Self::Select(a, i) => write!(f, "(select {} {})", a, i),
            Self::Store(a, i, v) => write!(f, "(store {} {} {})", a, i, v),
        }
    }
}
