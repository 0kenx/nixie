//! Term-to-polynomial extraction for CAD.
//!
//! Cylindrical Algebraic Decomposition operates on *polynomial* constraints
//! over the reals. This module turns arithmetic comparison atoms from the AST
//! into an explicit sparse multivariate [`CadPolynomial`] over `BigRational`,
//! walking `+`, `-`, `*`, unary negation, integer/rational constants,
//! variables, and integer powers (expressed as repeated multiplication).
//!
//! Terms that are not polynomial – division by a non-constant, modulo,
//! transcendental/uninterpreted applications, bit-vector or string operators,
//! and so on – are rejected with an explicit [`CadError`] rather than being
//! silently coerced into a bogus placeholder polynomial. This means a caller
//! can trust that a successfully extracted polynomial faithfully represents
//! `lhs - rhs` for the atom it came from.
//!
//! The full projection/lifting CAD pipeline that would turn these polynomials
//! into a quantifier-free equivalent is not implemented here; the base-case,
//! projection, lifting and sampling engines live in the sibling modules of
//! [`super`]. [`CadSolver::eliminate_quantifiers`] therefore performs the real
//! polynomial-extraction phase and then returns an honest
//! [`CadError::Unsupported`] instead of a fabricated result.
//!
//! Reference: Collins, "Quantifier Elimination for Real Closed Fields by
//! Cylindrical Algebraic Decomposition" (1975); Z3's `nlsat`/`qe` polynomial
//! handling.

use crate::ast::{TermId, TermKind, TermManager};
#[allow(unused_imports)]
use crate::prelude::*;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};
use std::collections::BTreeMap;
use std::fmt;

/// Errors produced while extracting polynomials for CAD.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CadError {
    /// A referenced term id was not present in the manager.
    InvalidTerm,
    /// The term is not a polynomial (e.g. non-constant division, modulo,
    /// an uninterpreted function, or a non-arithmetic operator).
    NonPolynomial(String),
    /// Division by a polynomial that is not a non-zero constant.
    DivisionByNonConstant,
    /// A supported-in-principle construct that this restricted pipeline does
    /// not yet handle (kept honest rather than fabricating a result).
    Unsupported(String),
}

impl fmt::Display for CadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CadError::InvalidTerm => write!(f, "invalid term id"),
            CadError::NonPolynomial(what) => write!(f, "not a polynomial: {what}"),
            CadError::DivisionByNonConstant => write!(f, "division by non-constant polynomial"),
            CadError::Unsupported(what) => write!(f, "unsupported for CAD: {what}"),
        }
    }
}

impl std::error::Error for CadError {}

/// A monomial: a sorted list of `(variable, exponent)` factors with exponent
/// `>= 1`. The empty vector denotes the constant monomial `1`.
type Monomial = Vec<(String, u32)>;

/// A sparse multivariate polynomial over `BigRational`.
///
/// Represented as a map from `Monomial` to a non-zero coefficient. The
/// canonical form keeps only non-zero coefficients, so `is_zero` is exactly
/// "no monomials".
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CadPolynomial {
    monomials: BTreeMap<Monomial, BigRational>,
}

impl CadPolynomial {
    /// The zero polynomial.
    pub fn zero() -> Self {
        Self {
            monomials: BTreeMap::new(),
        }
    }

    /// A constant polynomial.
    pub fn constant(value: BigRational) -> Self {
        let mut p = Self::zero();
        if !value.is_zero() {
            p.monomials.insert(Vec::new(), value);
        }
        p
    }

    /// A single variable `v` (i.e. the polynomial `v`).
    pub fn variable(name: &str) -> Self {
        let mut p = Self::zero();
        p.monomials
            .insert(vec![(name.to_string(), 1)], BigRational::one());
        p
    }

    /// Whether this is the zero polynomial.
    pub fn is_zero(&self) -> bool {
        self.monomials.is_empty()
    }

    /// If this polynomial is a constant, return its value (including zero).
    pub fn as_constant(&self) -> Option<BigRational> {
        match self.monomials.len() {
            0 => Some(BigRational::zero()),
            // Constant iff the single monomial is the empty (`1`) monomial.
            1 => self.monomials.get::<Monomial>(&Vec::new()).cloned(),
            _ => None,
        }
    }

    /// Total degree (the maximum sum of exponents over all monomials).
    pub fn degree(&self) -> u32 {
        self.monomials
            .keys()
            .map(|m| m.iter().map(|(_, e)| *e).sum::<u32>())
            .max()
            .unwrap_or(0)
    }

    /// The set of variables occurring in this polynomial.
    pub fn variables(&self) -> std::collections::BTreeSet<String> {
        let mut set = std::collections::BTreeSet::new();
        for m in self.monomials.keys() {
            for (v, _) in m {
                set.insert(v.clone());
            }
        }
        set
    }

    /// Number of (non-zero) monomials.
    pub fn len(&self) -> usize {
        self.monomials.len()
    }

    /// Whether the polynomial has no monomials (equivalent to [`Self::is_zero`]).
    pub fn is_empty(&self) -> bool {
        self.monomials.is_empty()
    }

    /// Insert `coeff * monomial`, folding into any existing monomial and
    /// dropping the entry if the coefficient becomes zero.
    fn add_monomial(&mut self, mut monomial: Monomial, coeff: BigRational) {
        if coeff.is_zero() {
            return;
        }
        // Canonicalize: sort factors and merge duplicate variables.
        monomial.sort();
        let mut merged: Monomial = Vec::with_capacity(monomial.len());
        for (var, exp) in monomial {
            if let Some(last) = merged.last_mut()
                && last.0 == var
            {
                last.1 += exp;
                continue;
            }
            merged.push((var, exp));
        }
        match self.monomials.get_mut(&merged) {
            Some(existing) => {
                *existing += coeff;
                if existing.is_zero() {
                    self.monomials.remove(&merged);
                }
            }
            None => {
                self.monomials.insert(merged, coeff);
            }
        }
    }

    /// Polynomial addition.
    pub fn add(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for (m, c) in &other.monomials {
            result.add_monomial(m.clone(), c.clone());
        }
        result
    }

    /// Polynomial negation.
    pub fn neg(&self) -> Self {
        let mut result = Self::zero();
        for (m, c) in &self.monomials {
            result.monomials.insert(m.clone(), -c.clone());
        }
        result
    }

    /// Polynomial subtraction.
    pub fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    /// Polynomial multiplication.
    pub fn mul(&self, other: &Self) -> Self {
        let mut result = Self::zero();
        for (m1, c1) in &self.monomials {
            for (m2, c2) in &other.monomials {
                let mut m = m1.clone();
                m.extend(m2.iter().cloned());
                result.add_monomial(m, c1 * c2);
            }
        }
        result
    }

    /// Divide by a non-zero *constant* polynomial. Returns
    /// [`CadError::DivisionByNonConstant`] otherwise.
    pub fn div_constant(&self, other: &Self) -> Result<Self, CadError> {
        let denom = match other.as_constant() {
            Some(c) if !c.is_zero() => c,
            _ => return Err(CadError::DivisionByNonConstant),
        };
        let mut result = Self::zero();
        for (m, c) in &self.monomials {
            result.monomials.insert(m.clone(), c / &denom);
        }
        Ok(result)
    }

    /// Evaluate the polynomial at a rational assignment. Variables missing
    /// from `point` are treated as `0`.
    pub fn evaluate(&self, point: &std::collections::HashMap<String, BigRational>) -> BigRational {
        let mut total = BigRational::zero();
        for (m, c) in &self.monomials {
            let mut term = c.clone();
            for (var, exp) in m {
                let value = point.get(var).cloned().unwrap_or_else(BigRational::zero);
                for _ in 0..*exp {
                    term *= &value;
                }
            }
            total += term;
        }
        total
    }
}

impl Default for CadPolynomial {
    fn default() -> Self {
        Self::zero()
    }
}

/// A polynomial constraint extracted from a comparison atom: `poly (op) 0`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PolynomialConstraint {
    /// The polynomial `lhs - rhs`.
    pub poly: CadPolynomial,
    /// The comparison relation applied against zero.
    pub relation: Relation,
}

/// Comparison relation of a polynomial constraint against zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Relation {
    /// `poly = 0`
    Eq,
    /// `poly < 0`
    Lt,
    /// `poly <= 0`
    Le,
}

/// Statistics for CAD polynomial extraction.
#[derive(Clone, Debug, Default)]
pub struct CadStats {
    /// Number of eliminate calls.
    pub total_eliminations: usize,
    /// Number of polynomial constraints extracted.
    pub total_polynomials: usize,
}

/// CAD solver front-end.
///
/// Currently exposes the (real) polynomial-extraction phase; the projection /
/// lifting pipeline is not wired in, so [`Self::eliminate_quantifiers`] returns
/// an honest [`CadError::Unsupported`].
#[derive(Debug, Default)]
pub struct CadSolver {
    stats: CadStats,
}

impl CadSolver {
    /// Create a new CAD solver.
    pub fn new() -> Self {
        Self::default()
    }

    /// Extract all polynomial constraints from a Boolean combination of
    /// arithmetic comparison atoms.
    ///
    /// Walks through `and`/`or`/`not` and, at each `=`/`<`/`<=`/`>`/`>=`
    /// atom, extracts `lhs - rhs` as a [`CadPolynomial`]. Non-polynomial atoms
    /// abort the whole extraction with an error rather than silently dropping
    /// or fabricating them.
    pub fn extract_polynomials(
        &mut self,
        formula: TermId,
        tm: &TermManager,
    ) -> Result<Vec<PolynomialConstraint>, CadError> {
        let mut out = Vec::new();
        self.collect_constraints(formula, tm, &mut out)?;
        self.stats.total_polynomials += out.len();
        Ok(out)
    }

    fn collect_constraints(
        &self,
        term: TermId,
        tm: &TermManager,
        out: &mut Vec<PolynomialConstraint>,
    ) -> Result<(), CadError> {
        let t = tm.get(term).ok_or(CadError::InvalidTerm)?;
        match &t.kind {
            TermKind::True | TermKind::False => Ok(()),
            TermKind::And(args) | TermKind::Or(args) => {
                for &arg in args.iter() {
                    self.collect_constraints(arg, tm, out)?;
                }
                Ok(())
            }
            TermKind::Not(arg) => self.collect_constraints(*arg, tm, out),
            TermKind::Eq(lhs, rhs) => {
                out.push(PolynomialConstraint {
                    poly: self.term_to_polynomial(*lhs, *rhs, tm)?,
                    relation: Relation::Eq,
                });
                Ok(())
            }
            TermKind::Lt(lhs, rhs) => {
                out.push(PolynomialConstraint {
                    poly: self.term_to_polynomial(*lhs, *rhs, tm)?,
                    relation: Relation::Lt,
                });
                Ok(())
            }
            TermKind::Le(lhs, rhs) => {
                out.push(PolynomialConstraint {
                    poly: self.term_to_polynomial(*lhs, *rhs, tm)?,
                    relation: Relation::Le,
                });
                Ok(())
            }
            // `a > b` is `b - a < 0`, `a >= b` is `b - a <= 0`.
            TermKind::Gt(lhs, rhs) => {
                out.push(PolynomialConstraint {
                    poly: self.term_to_polynomial(*rhs, *lhs, tm)?,
                    relation: Relation::Lt,
                });
                Ok(())
            }
            TermKind::Ge(lhs, rhs) => {
                out.push(PolynomialConstraint {
                    poly: self.term_to_polynomial(*rhs, *lhs, tm)?,
                    relation: Relation::Le,
                });
                Ok(())
            }
            other => Err(CadError::NonPolynomial(format!("{other:?}"))),
        }
    }

    /// Convert the comparison `lhs (op) rhs` into the polynomial `lhs - rhs`.
    pub fn term_to_polynomial(
        &self,
        lhs: TermId,
        rhs: TermId,
        tm: &TermManager,
    ) -> Result<CadPolynomial, CadError> {
        let lp = self.build_polynomial(lhs, tm)?;
        let rp = self.build_polynomial(rhs, tm)?;
        Ok(lp.sub(&rp))
    }

    /// Recursively build a polynomial from an arithmetic term.
    fn build_polynomial(&self, term: TermId, tm: &TermManager) -> Result<CadPolynomial, CadError> {
        let t = tm.get(term).ok_or(CadError::InvalidTerm)?;
        match &t.kind {
            TermKind::IntConst(n) => Ok(CadPolynomial::constant(BigRational::from_integer(
                n.clone(),
            ))),
            TermKind::RealConst(r) => Ok(CadPolynomial::constant(BigRational::new(
                BigInt::from(*r.numer()),
                BigInt::from(*r.denom()),
            ))),
            TermKind::Var(spur) => Ok(CadPolynomial::variable(tm.resolve_str(*spur))),
            TermKind::Neg(a) => Ok(self.build_polynomial(*a, tm)?.neg()),
            TermKind::Add(args) => {
                let mut acc = CadPolynomial::zero();
                for &arg in args.iter() {
                    acc = acc.add(&self.build_polynomial(arg, tm)?);
                }
                Ok(acc)
            }
            TermKind::Sub(a, b) => {
                let pa = self.build_polynomial(*a, tm)?;
                let pb = self.build_polynomial(*b, tm)?;
                Ok(pa.sub(&pb))
            }
            TermKind::Mul(args) => {
                let mut acc = CadPolynomial::constant(BigRational::one());
                for &arg in args.iter() {
                    acc = acc.mul(&self.build_polynomial(arg, tm)?);
                }
                Ok(acc)
            }
            TermKind::Div(a, b) => {
                let pa = self.build_polynomial(*a, tm)?;
                let pb = self.build_polynomial(*b, tm)?;
                pa.div_constant(&pb)
            }
            other => Err(CadError::NonPolynomial(format!("{other:?}"))),
        }
    }

    /// Eliminate quantifiers using CAD.
    ///
    /// Performs the real polynomial-extraction phase (which validates that the
    /// input is genuinely a polynomial formula) and then returns an honest
    /// [`CadError::Unsupported`], because the projection/lifting pipeline that
    /// would produce a quantifier-free equivalent is not implemented in this
    /// restricted front-end. It never returns a fabricated formula.
    pub fn eliminate_quantifiers(
        &mut self,
        formula: TermId,
        _quantified_vars: &[usize],
        tm: &mut TermManager,
    ) -> Result<TermId, CadError> {
        self.stats.total_eliminations += 1;
        // Validate the input is a real polynomial formula; this surfaces
        // NonPolynomial errors instead of hiding them.
        let _polynomials = self.extract_polynomials(formula, tm)?;
        Err(CadError::Unsupported(
            "full CAD projection/lifting is not implemented in this front-end".to_string(),
        ))
    }

    /// Get solver statistics.
    pub fn stats(&self) -> &CadStats {
        &self.stats
    }

    /// Reset solver statistics.
    pub fn reset(&mut self) {
        self.stats = CadStats::default();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_rational::Rational64;
    use std::collections::HashMap;

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(n))
    }

    #[test]
    fn test_solver_creation() {
        let solver = CadSolver::new();
        assert_eq!(solver.stats().total_eliminations, 0);
    }

    #[test]
    fn test_constant_extraction() {
        let mut tm = TermManager::new();
        let solver = CadSolver::new();
        let five = tm.mk_int(5);
        let three = tm.mk_int(3);
        // lhs - rhs = 5 - 3 = 2
        let p = solver
            .term_to_polynomial(five, three, &tm)
            .expect("constant polynomial");
        assert_eq!(p.as_constant(), Some(rat(2)));
        assert_eq!(p.degree(), 0);
    }

    #[test]
    fn test_linear_extraction_and_eval() {
        // Term: (2*x + 3*y) - (x - 1) = x + 3y + 1
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("x", int_sort);
        let y = tm.mk_var("y", int_sort);
        let two = tm.mk_int(2);
        let three = tm.mk_int(3);
        let one = tm.mk_int(1);
        let two_x = tm.mk_mul([two, x]);
        let three_y = tm.mk_mul([three, y]);
        let lhs = tm.mk_add([two_x, three_y]);
        let rhs = tm.mk_sub(x, one);

        let solver = CadSolver::new();
        let p = solver
            .term_to_polynomial(lhs, rhs, &tm)
            .expect("linear polynomial");
        assert_eq!(p.degree(), 1);

        // Equivalence check: evaluate the extracted polynomial at several
        // points and compare against lhs - rhs computed directly.
        for (xv, yv) in [(0i64, 0i64), (1, 2), (-3, 5), (7, -4)] {
            let mut point = HashMap::new();
            point.insert("x".to_string(), rat(xv));
            point.insert("y".to_string(), rat(yv));
            let expected = rat(xv) + rat(3) * rat(yv) + rat(1);
            assert_eq!(p.evaluate(&point), expected, "at x={xv}, y={yv}");
        }
    }

    #[test]
    fn test_quadratic_extraction_and_eval() {
        // Term: (x * x) - (2 * x) = x^2 - 2x
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("x", int_sort);
        let two = tm.mk_int(2);
        let x_sq = tm.mk_mul([x, x]);
        let two_x = tm.mk_mul([two, x]);

        let solver = CadSolver::new();
        let p = solver
            .term_to_polynomial(x_sq, two_x, &tm)
            .expect("quadratic polynomial");
        assert_eq!(p.degree(), 2);

        for xv in [-2i64, 0, 1, 3, 10] {
            let mut point = HashMap::new();
            point.insert("x".to_string(), rat(xv));
            let expected = rat(xv) * rat(xv) - rat(2) * rat(xv);
            assert_eq!(p.evaluate(&point), expected, "at x={xv}");
        }
    }

    #[test]
    fn test_real_constant_extraction() {
        let mut tm = TermManager::new();
        let real_sort = tm.sorts.real_sort;
        let x = tm.mk_var("x", real_sort);
        let half = tm.mk_real(Rational64::new(1, 2));
        // (x) - (1/2)
        let solver = CadSolver::new();
        let p = solver.term_to_polynomial(x, half, &tm).expect("polynomial");
        let mut point = HashMap::new();
        point.insert("x".to_string(), rat(3));
        // 3 - 1/2 = 5/2
        assert_eq!(
            p.evaluate(&point),
            BigRational::new(BigInt::from(5), BigInt::from(2))
        );
    }

    #[test]
    fn test_division_by_constant_ok() {
        // (6 * x) / 2 = 3x
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("x", int_sort);
        let six = tm.mk_int(6);
        let two = tm.mk_int(2);
        let six_x = tm.mk_mul([six, x]);
        let div = tm.mk_div(six_x, two);
        let zero = tm.mk_int(0);

        let solver = CadSolver::new();
        let p = solver
            .term_to_polynomial(div, zero, &tm)
            .expect("polynomial");
        let mut point = HashMap::new();
        point.insert("x".to_string(), rat(4));
        assert_eq!(p.evaluate(&point), rat(12)); // 3 * 4
    }

    #[test]
    fn test_division_by_variable_rejected() {
        // x / y is not a polynomial.
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("x", int_sort);
        let y = tm.mk_var("y", int_sort);
        let div = tm.mk_div(x, y);
        let zero = tm.mk_int(0);

        let solver = CadSolver::new();
        assert_eq!(
            solver.term_to_polynomial(div, zero, &tm),
            Err(CadError::DivisionByNonConstant)
        );
    }

    #[test]
    fn test_non_polynomial_rejected() {
        // mod is not polynomial.
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("x", int_sort);
        let two = tm.mk_int(2);
        let m = tm.mk_mod(x, two);
        let zero = tm.mk_int(0);

        let solver = CadSolver::new();
        assert!(matches!(
            solver.term_to_polynomial(m, zero, &tm),
            Err(CadError::NonPolynomial(_))
        ));
    }

    #[test]
    fn test_extract_polynomials_from_formula() {
        // (x >= 0) AND (x + y = 3)
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("x", int_sort);
        let y = tm.mk_var("y", int_sort);
        let zero = tm.mk_int(0);
        let three = tm.mk_int(3);
        let ge = tm.mk_ge(x, zero);
        let sum = tm.mk_add([x, y]);
        let eq = tm.mk_eq(sum, three);
        let formula = tm.mk_and([ge, eq]);

        let mut solver = CadSolver::new();
        let constraints = solver
            .extract_polynomials(formula, &tm)
            .expect("polynomial constraints");
        assert_eq!(constraints.len(), 2);
    }

    #[test]
    fn test_eliminate_quantifiers_is_honest() {
        // Real polynomial input -> honest Unsupported, never a fabricated term.
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("x", int_sort);
        let zero = tm.mk_int(0);
        let ge = tm.mk_ge(x, zero);

        let mut solver = CadSolver::new();
        assert!(matches!(
            solver.eliminate_quantifiers(ge, &[0], &mut tm),
            Err(CadError::Unsupported(_))
        ));

        // Non-polynomial input -> the error is surfaced, not hidden.
        let two = tm.mk_int(2);
        let m = tm.mk_mod(x, two);
        let bad = tm.mk_eq(m, zero);
        assert!(matches!(
            solver.eliminate_quantifiers(bad, &[0], &mut tm),
            Err(CadError::NonPolynomial(_))
        ));
    }

    #[test]
    fn test_polynomial_arithmetic_identities() {
        // (x + 1)(x - 1) = x^2 - 1
        let x_plus_1 = CadPolynomial::variable("x").add(&CadPolynomial::constant(rat(1)));
        let x_minus_1 = CadPolynomial::variable("x").sub(&CadPolynomial::constant(rat(1)));
        let product = x_plus_1.mul(&x_minus_1);

        let expected = CadPolynomial::variable("x")
            .mul(&CadPolynomial::variable("x"))
            .sub(&CadPolynomial::constant(rat(1)));
        assert_eq!(product, expected);
        assert_eq!(product.degree(), 2);
    }
}
