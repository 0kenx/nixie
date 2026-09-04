//! Node coloring and the A/B premise partition used for interpolation.

use crate::premise::PremiseId;
use rustc_hash::FxHashSet;
use std::fmt;

/// Color of a proof node in the interpolation procedure
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InterpolantColor {
    /// Node depends only on A premises
    A,
    /// Node depends only on B premises
    B,
    /// Node depends on both A and B premises (mixed)
    AB,
}

impl fmt::Display for InterpolantColor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::A => write!(f, "A"),
            Self::B => write!(f, "B"),
            Self::AB => write!(f, "AB"),
        }
    }
}

/// A partition of premises into A-side and B-side
#[derive(Debug, Clone)]
pub struct InterpolantPartition {
    /// Premises in the A partition
    a_premises: FxHashSet<PremiseId>,
    /// Premises in the B partition
    b_premises: FxHashSet<PremiseId>,
    /// Shared symbols between A and B
    shared_symbols: FxHashSet<Symbol>,
}

/// Symbol identifier (variable or function symbol)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Symbol {
    /// Symbol name
    pub name: String,
    /// Symbol arity (0 for constants/variables)
    pub arity: usize,
}

impl Symbol {
    /// Create a new symbol
    #[must_use]
    pub fn new(name: impl Into<String>, arity: usize) -> Self {
        Self {
            name: name.into(),
            arity,
        }
    }

    /// Create a variable symbol
    #[must_use]
    pub fn var(name: impl Into<String>) -> Self {
        Self::new(name, 0)
    }
}

impl InterpolantPartition {
    /// Create a new partition
    #[must_use]
    pub fn new(
        a_premises: impl IntoIterator<Item = PremiseId>,
        b_premises: impl IntoIterator<Item = PremiseId>,
    ) -> Self {
        Self {
            a_premises: a_premises.into_iter().collect(),
            b_premises: b_premises.into_iter().collect(),
            shared_symbols: FxHashSet::default(),
        }
    }

    /// Set shared symbols
    pub fn set_shared_symbols(&mut self, symbols: impl IntoIterator<Item = Symbol>) {
        self.shared_symbols = symbols.into_iter().collect();
    }

    /// Check if a premise is in the A partition
    #[must_use]
    pub fn is_a_premise(&self, premise: PremiseId) -> bool {
        self.a_premises.contains(&premise)
    }

    /// Check if a premise is in the B partition
    #[must_use]
    pub fn is_b_premise(&self, premise: PremiseId) -> bool {
        self.b_premises.contains(&premise)
    }

    /// Check if a symbol is shared
    #[must_use]
    pub fn is_shared(&self, symbol: &Symbol) -> bool {
        self.shared_symbols.contains(symbol)
    }

    /// Get A premises
    #[must_use]
    pub fn a_premises(&self) -> &FxHashSet<PremiseId> {
        &self.a_premises
    }

    /// Get B premises
    #[must_use]
    pub fn b_premises(&self) -> &FxHashSet<PremiseId> {
        &self.b_premises
    }

    /// Get the explicitly declared shared/global symbols.
    #[must_use]
    pub fn shared_symbols(&self) -> &FxHashSet<Symbol> {
        &self.shared_symbols
    }
}
