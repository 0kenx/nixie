//! Arithmetic Quantifier Elimination.
//!
//! This module implements quantifier elimination procedures for linear
//! arithmetic over integers and reals.

use crate::ast::{TermId, TermKind, TermManager};
#[allow(unused_imports)]
use crate::prelude::*;

pub mod cooper;
pub mod ferrante_rackoff;
pub(crate) mod lra;
pub mod omega_test;
pub mod qe_lite_arith;
pub mod virtual_term;

pub use cooper::{CooperEliminator, CooperStats};
pub use ferrante_rackoff::{
    FerranteRackoffEliminator, FerranteRackoffStats, Inequality, InequalityType,
};
pub use omega_test::{
    LinearConstraint as OmegaLinearConstraint, OmegaResult, OmegaTestConfig as OmegaConfig,
    OmegaTestStats as OmegaStats, OmegaTester as OmegaTest,
};
pub use virtual_term::{VirtualTermEliminator, VirtualTermStats};

/// Outcome of [`eliminate_linear`].
///
/// The two variants are kept distinct so that a caller can never mistake an
/// unmodified formula (elimination not applicable) for a genuinely eliminated
/// one: `NotApplied` always still contains the quantified variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LinearElimResult {
    /// The variable was eliminated: the contained formula is equivalent to
    /// `∃var. formula` and does **not** mention `var`.
    Eliminated(TermId),
    /// Elimination was not applicable (the variable is not a plain arithmetic
    /// variable, or the formula lies outside the supported linear fragment).
    /// The original formula is returned unchanged and still mentions `var`.
    NotApplied(TermId),
}

impl LinearElimResult {
    /// The resulting term in either case.
    pub fn term(self) -> TermId {
        match self {
            LinearElimResult::Eliminated(t) | LinearElimResult::NotApplied(t) => t,
        }
    }

    /// Whether the variable was genuinely eliminated.
    pub fn is_eliminated(self) -> bool {
        matches!(self, LinearElimResult::Eliminated(_))
    }
}

/// Eliminate one existentially-quantified linear arithmetic variable.
///
/// Integer variables are handled by Cooper's algorithm and real variables by
/// Loos–Weispfenning virtual substitution. When elimination is not possible –
/// `var` is not a plain arithmetic variable, or the formula is outside the
/// supported linear fragment – the original formula is returned as
/// [`LinearElimResult::NotApplied`] rather than being silently presented as an
/// eliminated result.
pub fn eliminate_linear(var: TermId, formula: TermId, tm: &mut TermManager) -> LinearElimResult {
    let (spur, sort) = match tm.get(var) {
        Some(term) => match &term.kind {
            TermKind::Var(s) => (*s, term.sort),
            _ => return LinearElimResult::NotApplied(formula),
        },
        None => return LinearElimResult::NotApplied(formula),
    };
    let name = tm.resolve_str(spur).to_string();

    if sort == tm.sorts.int_sort {
        let mut elim = cooper::CooperEliminator::new();
        match elim.eliminate_exists(name, formula, tm) {
            Ok(result) => LinearElimResult::Eliminated(result),
            Err(_) => LinearElimResult::NotApplied(formula),
        }
    } else if sort == tm.sorts.real_sort {
        let mut elim = virtual_term::VirtualTermEliminator::new();
        match elim.eliminate_exists(name, formula, tm) {
            Ok(result) => LinearElimResult::Eliminated(result),
            Err(_) => LinearElimResult::NotApplied(formula),
        }
    } else {
        LinearElimResult::NotApplied(formula)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eliminate_linear_int_uses_cooper() {
        // ∃x:Int. 2x = y   ≡   y even; the variable must disappear.
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("x", int_sort);
        let y = tm.mk_var("y", int_sort);
        let two = tm.mk_int(2);
        let two_x = tm.mk_mul(vec![two, x]);
        let phi = tm.mk_eq(two_x, y);

        let result = eliminate_linear(x, phi, &mut tm);
        assert!(result.is_eliminated());
        let x_spur = tm.intern_str("x");
        assert!(!lra::mentions_var(result.term(), x_spur, &tm));
    }

    #[test]
    fn eliminate_linear_real_uses_virtual_substitution() {
        // ∃x:Real. (x > 0) ∧ (x < 1)   → true.
        let mut tm = TermManager::new();
        let real_sort = tm.sorts.real_sort;
        let x = tm.mk_var("x", real_sort);
        let zero = tm.mk_real(num_rational::Rational64::new(0, 1));
        let one = tm.mk_real(num_rational::Rational64::new(1, 1));
        let c1 = tm.mk_gt(x, zero);
        let c2 = tm.mk_lt(x, one);
        let phi = tm.mk_and(vec![c1, c2]);

        let result = eliminate_linear(x, phi, &mut tm);
        assert!(result.is_eliminated());
        let x_spur = tm.intern_str("x");
        assert!(!lra::mentions_var(result.term(), x_spur, &tm));
    }

    #[test]
    fn eliminate_linear_reports_not_applied_on_nonlinear() {
        // ∃x:Int. x*x = y  is outside the linear fragment: NotApplied, and the
        // returned formula still mentions x.
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("x", int_sort);
        let y = tm.mk_var("y", int_sort);
        let xx = tm.mk_mul(vec![x, x]);
        let phi = tm.mk_eq(xx, y);

        let result = eliminate_linear(x, phi, &mut tm);
        assert!(!result.is_eliminated());
        assert_eq!(result.term(), phi);
        let x_spur = tm.intern_str("x");
        assert!(lra::mentions_var(result.term(), x_spur, &tm));
    }

    #[test]
    fn eliminate_linear_reports_not_applied_on_non_variable() {
        let mut tm = TermManager::new();
        let five = tm.mk_int(5);
        let ten = tm.mk_int(10);
        let phi = tm.mk_lt(five, ten);
        // `five` is not a variable term.
        let result = eliminate_linear(five, phi, &mut tm);
        assert!(!result.is_eliminated());
        assert_eq!(result.term(), phi);
    }
}
