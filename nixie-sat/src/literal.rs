//! Literals and Variables

#[allow(unused_imports)]
use crate::prelude::*;
use core::ops::Not;

/// A variable in the SAT formula
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Var(pub u32);

impl Var {
    /// Largest index that fits the packed literal and both signed DIMACS forms.
    pub const MAX_INDEX: u32 = (1 << 31) - 2;

    /// Create a new variable from a raw index
    ///
    /// # Panics
    ///
    /// Panics in every build profile when `idx` exceeds [`Var::MAX_INDEX`].
    #[must_use]
    pub const fn new(idx: u32) -> Self {
        assert!(
            idx <= Self::MAX_INDEX,
            "variable index exceeds Var::MAX_INDEX"
        );
        Self(idx)
    }

    /// Get the raw index
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// A literal (positive or negative occurrence of a variable)
///
/// `#[repr(transparent)]` makes the layout identical to the inner `u32`,
/// which the clause arena (`memory.rs`) relies on when reading/writing
/// literal arrays packed after clause headers in a `u64` buffer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Lit(u32);

impl Lit {
    /// Create a positive literal from a variable
    ///
    /// # Panics
    ///
    /// Panics in every build profile when the index exceeds [`Var::MAX_INDEX`].
    #[must_use]
    pub const fn pos(var: Var) -> Self {
        assert!(
            var.0 <= Var::MAX_INDEX,
            "variable index exceeds Var::MAX_INDEX"
        );
        Self(var.0 << 1)
    }

    /// Create a negative literal from a variable
    ///
    /// # Panics
    ///
    /// Panics in every build profile when the index exceeds [`Var::MAX_INDEX`].
    #[must_use]
    pub const fn neg(var: Var) -> Self {
        assert!(
            var.0 <= Var::MAX_INDEX,
            "variable index exceeds Var::MAX_INDEX"
        );
        Self((var.0 << 1) | 1)
    }

    /// Create a literal from a signed integer (DIMACS format)
    /// Positive int -> positive literal, negative int -> negative literal
    ///
    /// # Panics
    ///
    /// Panics for zero and `i32::MIN`, which have no supported literal.
    #[must_use]
    pub fn from_dimacs(lit: i32) -> Self {
        assert!(lit != 0 && lit != i32::MIN, "invalid DIMACS literal");
        let var = Var::new(lit.unsigned_abs() - 1);
        if lit > 0 {
            Self::pos(var)
        } else {
            Self::neg(var)
        }
    }

    /// Convert to DIMACS format
    ///
    /// # Panics
    ///
    /// Panics in every build profile when the raw encoding exceeds [`Var::MAX_INDEX`]. Use [`Lit::try_to_dimacs`] to handle this as `None`.
    #[must_use]
    pub fn to_dimacs(self) -> i32 {
        match self.try_to_dimacs() {
            Some(lit) => lit,
            None => panic!("Lit::to_dimacs: variable index exceeds Var::MAX_INDEX"),
        }
    }

    /// Convert to DIMACS without panicking, rejecting an unrepresentable magnitude.
    ///
    /// Raw encodings created by [`Lit::from_code`] can exceed [`Var::MAX_INDEX`].
    #[must_use]
    pub fn try_to_dimacs(self) -> Option<i32> {
        let magnitude = i32::try_from(self.var().0.checked_add(1)?).ok()?;
        Some(if self.is_pos() { magnitude } else { -magnitude })
    }

    /// Get the variable of this literal
    #[must_use]
    pub const fn var(self) -> Var {
        Var(self.0 >> 1)
    }

    /// Check if this is a positive literal
    #[must_use]
    pub const fn is_pos(self) -> bool {
        (self.0 & 1) == 0
    }

    /// Check if this is a negative literal
    #[must_use]
    pub const fn is_neg(self) -> bool {
        (self.0 & 1) == 1
    }

    /// Get the negation of this literal
    #[must_use]
    pub const fn negate(self) -> Self {
        Self(self.0 ^ 1)
    }

    /// Get the sign (true for positive, false for negative)
    #[must_use]
    pub const fn sign(self) -> bool {
        self.is_pos()
    }

    /// Get the raw encoding
    #[must_use]
    pub const fn code(self) -> u32 {
        self.0
    }

    /// Create from raw encoding
    #[must_use]
    pub const fn from_code(code: u32) -> Self {
        Self(code)
    }

    /// Get the index for array access (2 * var + sign)
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

impl Not for Lit {
    type Output = Self;

    fn not(self) -> Self::Output {
        self.negate()
    }
}

/// Boolean value or undefined
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LBool {
    /// True
    True,
    /// False
    False,
    /// Undefined
    Undef,
}

impl LBool {
    /// Create from a boolean
    #[must_use]
    pub const fn from_bool(b: bool) -> Self {
        if b { Self::True } else { Self::False }
    }

    /// Check if defined
    #[must_use]
    pub const fn is_defined(self) -> bool {
        !matches!(self, Self::Undef)
    }

    /// Check if true
    #[must_use]
    pub const fn is_true(self) -> bool {
        matches!(self, Self::True)
    }

    /// Check if false
    #[must_use]
    pub const fn is_false(self) -> bool {
        matches!(self, Self::False)
    }

    /// Negate
    #[must_use]
    pub const fn negate(self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Undef => Self::Undef,
        }
    }
}

impl From<bool> for LBool {
    fn from(b: bool) -> Self {
        Self::from_bool(b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_literal_creation() {
        let var = Var::new(0);
        let pos = Lit::pos(var);
        let neg = Lit::neg(var);

        assert!(pos.is_pos());
        assert!(neg.is_neg());
        assert_eq!(pos.var(), var);
        assert_eq!(neg.var(), var);
        assert_eq!(pos.negate(), neg);
        assert_eq!(neg.negate(), pos);
    }

    #[test]
    fn test_dimacs_conversion() {
        let lit = Lit::from_dimacs(1);
        assert!(lit.is_pos());
        assert_eq!(lit.var(), Var::new(0));
        assert_eq!(lit.to_dimacs(), 1);

        let lit = Lit::from_dimacs(-2);
        assert!(lit.is_neg());
        assert_eq!(lit.var(), Var::new(1));
        assert_eq!(lit.to_dimacs(), -2);
    }

    #[test]
    fn dimacs_boundary_roundtrips() {
        for index in [0, 1, Var::MAX_INDEX] {
            let var = Var::new(index);
            for lit in [Lit::pos(var), Lit::neg(var)] {
                let value = lit.try_to_dimacs().expect("representable literal");
                assert_eq!(Lit::from_dimacs(value), lit);
                assert_eq!(lit.to_dimacs(), value);
            }
        }
        for code in [u32::MAX - 1, u32::MAX] {
            assert_eq!(Lit::from_code(code).try_to_dimacs(), None);
        }
    }

    #[test]
    fn invalid_literals_are_rejected_in_release_too() {
        for index in [Var::MAX_INDEX + 1, 1 << 31, u32::MAX] {
            assert!(std::panic::catch_unwind(|| Var::new(index)).is_err());
            assert!(std::panic::catch_unwind(|| Lit::pos(Var(index))).is_err());
            assert!(std::panic::catch_unwind(|| Lit::neg(Var(index))).is_err());
        }
        for value in [0, i32::MIN] {
            assert!(std::panic::catch_unwind(|| Lit::from_dimacs(value)).is_err());
        }
        for code in [u32::MAX - 1, u32::MAX] {
            assert!(std::panic::catch_unwind(|| Lit::from_code(code).to_dimacs()).is_err());
        }
    }

    #[test]
    fn test_lbool() {
        assert!(LBool::True.is_true());
        assert!(LBool::False.is_false());
        assert!(!LBool::Undef.is_defined());

        assert_eq!(LBool::True.negate(), LBool::False);
        assert_eq!(LBool::False.negate(), LBool::True);
        assert_eq!(LBool::Undef.negate(), LBool::Undef);
    }
}
