//! Ferrante–Rackoff algorithm for linear real-arithmetic quantifier elimination.
//!
//! Eliminates an existential quantifier `∃x. φ(x)`, where `φ` is a
//! quantifier-free boolean combination of linear comparison atoms over the
//! reals, by exploiting the fact that the truth value of `φ` as a function of
//! `x` is piecewise constant, with breakpoints only at the roots of the atoms.
//! It therefore suffices to test one representative from each maximal interval
//! of constant truth value:
//!
//! ```text
//! ∃x. φ(x)  ≡  φ(-∞)  ∨  φ(+∞)  ∨  ⋁_{a,b ∈ B, a ≤ b} φ((a + b)/2)
//! ```
//!
//! where `B` is the set of boundary terms (the value of `x` at which some atom
//! changes sign). Pairs with `a = b` recover the boundary points themselves;
//! pairs with `a < b` give an interior point of the interval between two
//! consecutive boundaries. All arithmetic is exact rational arithmetic.
//!
//! Formulae outside the supported linear-real fragment — a non-linear
//! occurrence of `x`, `x` under an uninterpreted symbol, or an integer-sorted
//! `x` (for which the dense-order midpoint construction is unsound) — are
//! reported as an explicit `Err` rather than silently returning an unchanged or
//! wrong result.
//!
//! Reference: Ferrante & Rackoff, *A decision procedure for the first order
//! theory of real addition with order* (SIAM J. Comput. 1975); Z3's
//! `qe_arith.cpp`.

use super::lra;
use crate::ast::{TermId, TermManager};
use crate::prelude::FxHashMap;
#[allow(unused_imports)]
use crate::prelude::*;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;

/// Ferrante–Rackoff QE engine for real arithmetic.
pub struct FerranteRackoffEliminator {
    /// Statistics
    stats: FerranteRackoffStats,
}

/// Inequality type in real arithmetic.
///
/// Retained as part of the public surface for callers that classify atoms
/// externally; the eliminator itself works over the shared linear-real-
/// arithmetic representation in `super::lra`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InequalityType {
    /// Strict less than: <
    Lt,
    /// Less than or equal: ≤
    Le,
    /// Strict greater than: >
    Gt,
    /// Greater than or equal: ≥
    Ge,
    /// Equality: =
    Eq,
    /// Disequality: ≠
    Ne,
}

/// Linear inequality representation.
///
/// Part of the public surface (see [`InequalityType`]).
#[derive(Debug, Clone)]
pub struct Inequality {
    /// Coefficients: a₁x₁ + a₂x₂ + ... + aₙxₙ
    pub coeffs: Vec<(String, BigRational)>,
    /// Constant term
    pub constant: BigRational,
    /// Inequality type
    pub ineq_type: InequalityType,
}

/// Ferrante–Rackoff statistics.
#[derive(Debug, Clone, Default)]
pub struct FerranteRackoffStats {
    /// Number of quantifiers eliminated
    pub quantifiers_eliminated: usize,
    /// Number of interior (interval-midpoint) tests
    pub infinitesimal_tests: usize,
    /// Number of boundary-point tests
    pub boundary_tests: usize,
    /// Number of infinity (±∞) tests
    pub infinity_tests: usize,
}

impl FerranteRackoffEliminator {
    /// Create a new Ferrante–Rackoff eliminator.
    pub fn new() -> Self {
        Self {
            stats: FerranteRackoffStats::default(),
        }
    }

    /// Eliminate an existential quantifier: `∃var. formula(var)`.
    ///
    /// On success returns a quantifier-free formula equivalent to
    /// `∃var. formula` in which `var` does not occur. Returns `Err` for
    /// formulae outside the supported linear-real fragment (soundness is
    /// preserved: no wrong or `var`-containing result is ever returned as
    /// `Ok`).
    pub fn eliminate_exists(
        &mut self,
        var: String,
        formula: TermId,
        tm: &mut TermManager,
    ) -> Result<TermId, String> {
        let x = tm.intern_str(&var);

        // If `x` does not occur, ∃x.φ ≡ φ.
        if !lra::mentions_var(formula, x, tm) {
            self.stats.quantifiers_eliminated += 1;
            return Ok(formula);
        }

        // Ferrante–Rackoff is a dense-order (real) method: the midpoint
        // `(a+b)/2` need not be an integer, so an integer-sorted `x` is
        // unsound. Reject it honestly.
        let real_sort = tm.sorts.real_sort;
        if lra::find_var_sort(formula, x, tm) != Some(real_sort) {
            return Err(
                "ferrante_rackoff: eliminated variable must be of real sort \
                 (use CooperEliminator for integers)"
                    .to_string(),
            );
        }

        // Collect the boundary terms from every atom mentioning `x`.
        let mut atoms = Vec::new();
        lra::collect_x_atoms(formula, x, tm, &mut atoms)?;

        let mut boundaries: Vec<TermId> = Vec::with_capacity(atoms.len());
        for a in &atoms {
            let b = lra::boundary_term(&a.x_coeff, &a.others, &a.constant, tm)
                .ok_or("ferrante_rackoff: coefficient too large to eliminate")?;
            boundaries.push(b);
        }
        boundaries.sort_by_key(|t| t.0);
        boundaries.dedup();

        let x_id = tm.mk_var(&var, real_sort);
        let mut disjuncts: Vec<TermId> = Vec::new();

        // Unbounded intervals: x → -∞ and x → +∞.
        let neg_inf = lra::inf_rewrite(formula, x, false, tm)?;
        disjuncts.push(neg_inf);
        self.stats.infinity_tests += 1;
        let pos_inf = lra::inf_rewrite(formula, x, true, tm)?;
        disjuncts.push(pos_inf);
        self.stats.infinity_tests += 1;

        // Midpoints (a + b)/2 for every ordered pair of boundaries; the
        // diagonal a = b recovers the boundary points themselves.
        let half = lra::mk_real_const(tm, &BigRational::new(BigInt::one(), BigInt::from(2)))
            .ok_or("ferrante_rackoff: internal error building 1/2")?;
        for i in 0..boundaries.len() {
            for j in i..boundaries.len() {
                let sum = tm.mk_add(vec![boundaries[i], boundaries[j]]);
                let mid = tm.mk_mul(vec![half, sum]);
                let mut subst = FxHashMap::default();
                subst.insert(x_id, mid);
                let substituted = tm.substitute(formula, &subst);
                disjuncts.push(tm.simplify(substituted));
                if i == j {
                    self.stats.boundary_tests += 1;
                } else {
                    self.stats.infinitesimal_tests += 1;
                }
            }
        }

        self.stats.quantifiers_eliminated += 1;
        let result = tm.mk_or(disjuncts);
        Ok(tm.simplify(result))
    }

    /// Get statistics.
    pub fn stats(&self) -> &FerranteRackoffStats {
        &self.stats
    }
}

impl Default for FerranteRackoffEliminator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::TermKind;
    use num_rational::Rational64;
    use num_traits::Zero;

    fn real_var(tm: &mut TermManager, name: &str) -> TermId {
        let real_sort = tm.sorts.real_sort;
        tm.mk_var(name, real_sort)
    }

    fn rl(tm: &mut TermManager, n: i64) -> TermId {
        tm.mk_real(Rational64::new(n, 1))
    }

    /// Exact-rational ground evaluator over the fragment the eliminator emits
    /// (formula must be free of the eliminated variable, and here also free of
    /// every other variable).
    fn eval_bool(tm: &TermManager, id: TermId) -> bool {
        fn num(tm: &TermManager, id: TermId) -> BigRational {
            match &tm.get(id).expect("term").kind {
                TermKind::IntConst(n) => BigRational::from_integer(n.clone()),
                TermKind::RealConst(r) => {
                    BigRational::new(BigInt::from(*r.numer()), BigInt::from(*r.denom()))
                }
                TermKind::Neg(a) => -num(tm, *a),
                TermKind::Add(args) => args
                    .iter()
                    .fold(BigRational::zero(), |acc, &a| acc + num(tm, a)),
                TermKind::Sub(a, b) => num(tm, *a) - num(tm, *b),
                TermKind::Mul(args) => args
                    .iter()
                    .fold(BigRational::one(), |acc, &a| acc * num(tm, a)),
                other => panic!("unexpected arithmetic term {other:?}"),
            }
        }
        match &tm.get(id).expect("term").kind {
            TermKind::True => true,
            TermKind::False => false,
            TermKind::Not(a) => !eval_bool(tm, *a),
            TermKind::And(args) => args.iter().all(|&a| eval_bool(tm, a)),
            TermKind::Or(args) => args.iter().any(|&a| eval_bool(tm, a)),
            TermKind::Implies(a, b) => !eval_bool(tm, *a) || eval_bool(tm, *b),
            TermKind::Lt(a, b) => num(tm, *a) < num(tm, *b),
            TermKind::Le(a, b) => num(tm, *a) <= num(tm, *b),
            TermKind::Gt(a, b) => num(tm, *a) > num(tm, *b),
            TermKind::Ge(a, b) => num(tm, *a) >= num(tm, *b),
            TermKind::Eq(a, b) => num(tm, *a) == num(tm, *b),
            other => panic!("unexpected boolean term {other:?}"),
        }
    }

    #[test]
    fn test_eliminator_starts_empty() {
        let e = FerranteRackoffEliminator::new();
        assert_eq!(e.stats().quantifiers_eliminated, 0);
    }

    #[test]
    fn bounded_open_interval_is_true() {
        // ∃x. (2 < x) ∧ (x < 4)   over the reals → true.
        let mut tm = TermManager::new();
        let x = real_var(&mut tm, "x");
        let two = rl(&mut tm, 2);
        let four = rl(&mut tm, 4);
        let c1 = tm.mk_lt(two, x);
        let c2 = tm.mk_lt(x, four);
        let phi = tm.mk_and(vec![c1, c2]);

        let mut e = FerranteRackoffEliminator::new();
        let result = e
            .eliminate_exists("x".to_string(), phi, &mut tm)
            .expect("elimination should succeed");
        let x_spur = tm.intern_str("x");
        assert!(!lra::mentions_var(result, x_spur, &tm), "x still present");
        assert!(eval_bool(&tm, result), "expected true");
    }

    #[test]
    fn empty_interval_is_false() {
        // ∃x. (4 < x) ∧ (x < 2)   → false.
        let mut tm = TermManager::new();
        let x = real_var(&mut tm, "x");
        let two = rl(&mut tm, 2);
        let four = rl(&mut tm, 4);
        let c1 = tm.mk_lt(four, x);
        let c2 = tm.mk_lt(x, two);
        let phi = tm.mk_and(vec![c1, c2]);

        let mut e = FerranteRackoffEliminator::new();
        let result = e
            .eliminate_exists("x".to_string(), phi, &mut tm)
            .expect("elimination should succeed");
        let x_spur = tm.intern_str("x");
        assert!(!lra::mentions_var(result, x_spur, &tm), "x still present");
        assert!(!eval_bool(&tm, result), "expected false");
    }

    #[test]
    fn degenerate_closed_point_is_true() {
        // ∃x. (x ≤ 3) ∧ (x ≥ 3)   → true (x = 3).
        let mut tm = TermManager::new();
        let x = real_var(&mut tm, "x");
        let three = rl(&mut tm, 3);
        let c1 = tm.mk_le(x, three);
        let c2 = tm.mk_ge(x, three);
        let phi = tm.mk_and(vec![c1, c2]);

        let mut e = FerranteRackoffEliminator::new();
        let result = e
            .eliminate_exists("x".to_string(), phi, &mut tm)
            .expect("elimination should succeed");
        assert!(eval_bool(&tm, result), "expected true");
    }

    #[test]
    fn open_point_hole_is_false() {
        // ∃x. (x ≤ 3) ∧ (x ≥ 3) ∧ (x ≠ 3)   → false.
        let mut tm = TermManager::new();
        let x = real_var(&mut tm, "x");
        let three = rl(&mut tm, 3);
        let c1 = tm.mk_le(x, three);
        let c2 = tm.mk_ge(x, three);
        let eq = tm.mk_eq(x, three);
        let c3 = tm.mk_not(eq);
        let phi = tm.mk_and(vec![c1, c2, c3]);

        let mut e = FerranteRackoffEliminator::new();
        let result = e
            .eliminate_exists("x".to_string(), phi, &mut tm)
            .expect("elimination should succeed");
        assert!(!eval_bool(&tm, result), "expected false");
    }

    #[test]
    fn integer_sort_is_rejected() {
        // ∃x:Int. x < 5 — Ferrante–Rackoff is a real method; reject honestly.
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("x", int_sort);
        let five = tm.mk_int(5);
        let phi = tm.mk_lt(x, five);

        let mut e = FerranteRackoffEliminator::new();
        assert!(
            e.eliminate_exists("x".to_string(), phi, &mut tm).is_err(),
            "integer sort must be rejected, not faked"
        );
    }

    #[test]
    fn nonlinear_is_rejected() {
        // ∃x. x*x = y — outside the linear fragment → honest Err.
        let mut tm = TermManager::new();
        let x = real_var(&mut tm, "x");
        let y = real_var(&mut tm, "y");
        let xx = tm.mk_mul(vec![x, x]);
        let phi = tm.mk_eq(xx, y);

        let mut e = FerranteRackoffEliminator::new();
        assert!(
            e.eliminate_exists("x".to_string(), phi, &mut tm).is_err(),
            "non-linear input must be rejected, not faked"
        );
    }

    #[test]
    fn x_free_formula_is_returned_unchanged() {
        // ∃x. (y < 3)  with x absent ≡ (y < 3).
        let mut tm = TermManager::new();
        let y = real_var(&mut tm, "y");
        let three = rl(&mut tm, 3);
        let phi = tm.mk_lt(y, three);

        let mut e = FerranteRackoffEliminator::new();
        let result = e
            .eliminate_exists("x".to_string(), phi, &mut tm)
            .expect("elimination should succeed");
        assert_eq!(result, phi);
    }
}
