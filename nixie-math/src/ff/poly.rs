//! Sparse multivariate polynomials over 𝔽_p (`docs/FF_THEORY_DESIGN.md` §4.4).
//!
//! A polynomial is a map from monomials (exponent vectors, reusing the
//! coefficient-agnostic parts of `nixie_math::polynomial::Monomial`) to
//! Montgomery-form coefficients. The 𝔽_p-specific `mul`/`add` reduce as
//! they go, so **coefficient growth does not exist here** — the pathology
//! that makes Gröbner bases over ℚ explode, and the reason the OKTB23
//! procedure works at all.
//!
//! Determinism: iteration over a polynomial's terms goes through
//! `sorted_terms` (monomial-ordered), never through hash-map order. Every
//! collection that feeds a Gröbner computation is index- or order-sorted.

use super::field::{FieldCtx, Limbs};
use crate::polynomial::{Monomial, MonomialOrder, Var};
use rustc_hash::FxHashMap;
use std::cmp::Ordering;

/// A sparse multivariate polynomial over one 𝔽_p.
#[derive(Debug, Clone)]
pub struct MPoly {
    terms: FxHashMap<Monomial, Limbs>,
}

impl PartialEq for MPoly {
    fn eq(&self, other: &Self) -> bool {
        self.terms.len() == other.terms.len()
            && self
                .terms
                .iter()
                .all(|(m, c)| other.terms.get(m).is_some_and(|d| d == c))
    }
}
impl Eq for MPoly {}

impl MPoly {
    /// The zero polynomial.
    #[must_use]
    pub fn zero() -> Self {
        Self {
            terms: FxHashMap::default(),
        }
    }

    /// Whether this is the zero polynomial.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// The number of (nonzero) terms.
    #[must_use]
    pub fn n_terms(&self) -> usize {
        self.terms.len()
    }

    /// A constant polynomial (the zero polynomial when `c` is zero).
    #[must_use]
    pub fn constant(f: &FieldCtx, c: &Limbs) -> Self {
        let mut p = Self::zero();
        p.add_term(f, Monomial::unit(), c);
        p
    }

    /// Iterate the terms in hash order — determinism-sensitive code must
    /// use [`MPoly::sorted_terms`] instead.
    pub fn terms_iter(&self) -> impl Iterator<Item = (&Monomial, &Limbs)> {
        self.terms.iter()
    }

    /// The coefficient of an exact monomial, if present.
    #[must_use]
    pub fn get_term(&self, m: &Monomial) -> Option<&Limbs> {
        self.terms.get(m)
    }

    /// Add one `coeff · monomial` term (accumulating an existing one; a
    /// cancelling coefficient removes the term).
    pub fn add_term(&mut self, f: &FieldCtx, monomial: Monomial, coeff: &Limbs) {
        if f.is_zero(coeff) {
            return;
        }
        let entry = self
            .terms
            .entry(monomial.clone())
            .or_insert_with(|| f.zero());
        *entry = f.add(entry, coeff);
        if f.is_zero(entry) {
            self.terms.remove(&monomial);
        }
    }

    /// The terms sorted by `order` (greatest first is the caller's choice;
    /// this returns ascending order — `sorted_terms` reversed gives the
    /// leading term first, which is how the Buchberger loop consumes it).
    pub fn sorted_terms(&self, order: MonomialOrder) -> Vec<(Monomial, Limbs)> {
        let mut terms: Vec<(Monomial, Limbs)> = self
            .terms
            .iter()
            .map(|(m, c)| (m.clone(), c.clone()))
            .collect();
        terms.sort_by(|a, b| order.compare(&a.0, &b.0));
        terms
    }

    /// The leading monomial under `order` (the greatest).
    #[must_use]
    pub fn lm(&self, order: MonomialOrder) -> Option<Monomial> {
        self.terms
            .keys()
            .max_by(|a, b| order.compare(a, b))
            .cloned()
    }

    /// The leading coefficient under `order`.
    #[must_use]
    pub fn lc(&self, order: MonomialOrder) -> Option<&Limbs> {
        self.lm(order).and_then(|m| self.terms.get(&m))
    }

    /// The constant term's coefficient (zero if absent).
    #[must_use]
    pub fn constant_term(&self, f: &FieldCtx) -> Limbs {
        let unit = Monomial::unit();
        self.terms.get(&unit).cloned().unwrap_or_else(|| f.zero())
    }

    /// Whether this is a nonzero constant.
    #[must_use]
    pub fn is_nonzero_constant(&self) -> bool {
        !self.terms.is_empty() && self.terms.keys().all(|m| m.total_degree() == 0)
    }

    /// Polynomial addition.
    #[must_use]
    pub fn add(&self, f: &FieldCtx, other: &Self) -> Self {
        let mut out = self.clone();
        for (m, c) in &other.terms {
            out.add_term(f, m.clone(), c);
        }
        out
    }

    /// Polynomial negation.
    #[must_use]
    pub fn neg(&self, f: &FieldCtx) -> Self {
        let mut out = Self::zero();
        for (m, c) in &self.terms {
            out.add_term(f, m.clone(), &f.neg(c));
        }
        out
    }

    /// Polynomial subtraction.
    #[must_use]
    pub fn sub(&self, f: &FieldCtx, other: &Self) -> Self {
        self.add(f, &other.neg(f))
    }

    /// Scalar multiple.
    #[must_use]
    pub fn scale(&self, f: &FieldCtx, s: &Limbs) -> Self {
        if f.is_zero(s) {
            return Self::zero();
        }
        let mut out = Self::zero();
        for (m, c) in &self.terms {
            out.add_term(f, m.clone(), &f.mul(c, s));
        }
        out
    }

    /// Polynomial multiplication (sparse × sparse; every product reduces
    /// mod p immediately).
    #[must_use]
    pub fn mul(&self, f: &FieldCtx, other: &Self) -> Self {
        let mut out = Self::zero();
        for (m1, c1) in &self.terms {
            for (m2, c2) in &other.terms {
                let coeff = f.mul(c1, c2);
                out.add_term(f, m1.mul(m2), &coeff);
            }
        }
        out
    }

    /// Monic normalization (divide through by the leading coefficient).
    /// The zero polynomial is unchanged.
    #[must_use]
    pub fn monic(&self, f: &FieldCtx, order: MonomialOrder) -> Self {
        match self.lc(order) {
            None => Self::zero(),
            Some(lc) => match f.inv(lc) {
                Some(inv) => self.scale(f, &inv),
                None => Self::zero(),
            },
        }
    }

    /// The exact set of variables appearing in this polynomial.
    #[must_use]
    pub fn variables(&self) -> Vec<Var> {
        let mut vars: Vec<Var> = Vec::new();
        for m in self.terms.keys() {
            for vp in m.vars() {
                if !vars.contains(&vp.var) {
                    vars.push(vp.var);
                }
            }
        }
        vars.sort_unstable();
        vars
    }

    /// Evaluate a variable at a field element.
    #[must_use]
    pub fn eval_var(&self, f: &FieldCtx, var: Var, value: &Limbs) -> Self {
        let mut out = Self::zero();
        for (m, c) in &self.terms {
            let mut new_m = Monomial::unit();
            let mut coeff = c.clone();
            for vp in m.vars() {
                if vp.var == var {
                    for _ in 0..vp.power {
                        coeff = f.mul(&coeff, value);
                    }
                } else {
                    new_m = new_m.mul(&Monomial::from_var_power(vp.var, vp.power));
                }
            }
            out.add_term(f, new_m, &coeff);
        }
        out
    }

    /// Substitute variables by values (all at once); returns a constant
    /// polynomial when every variable is substituted.
    #[must_use]
    pub fn eval_all(&self, f: &FieldCtx, assignment: &FxHashMap<Var, Limbs>) -> Limbs {
        let mut acc = f.zero();
        for (m, c) in &self.terms {
            let mut coeff = c.clone();
            for vp in m.vars() {
                if let Some(v) = assignment.get(&vp.var) {
                    for _ in 0..vp.power {
                        coeff = f.mul(&coeff, v);
                    }
                }
            }
            acc = f.add(&acc, &coeff);
        }
        acc
    }

    /// The total degree (max monomial total degree).
    #[must_use]
    pub fn total_degree(&self) -> u32 {
        self.terms
            .keys()
            .map(|m| m.total_degree())
            .max()
            .unwrap_or(0)
    }
}

/// Whether `a` is divisible by `b` (the exponent-wise divisibility of
/// monomials; `Monomial::div` computes the quotient).
#[must_use]
pub fn monomial_divides(a: &Monomial, b: &Monomial) -> bool {
    a.div(b).is_some()
}

/// `a / b` when divisible (exponent-wise subtraction).
#[must_use]
pub fn monomial_div(a: &Monomial, b: &Monomial) -> Option<Monomial> {
    a.div(b)
}

/// lcm of two monomials (max exponent per variable).
#[must_use]
pub fn monomial_lcm(a: &Monomial, b: &Monomial) -> Monomial {
    Monomial::from_powers(
        a.vars().iter().map(|vp| (vp.var, vp.power)).chain(
            b.vars()
                .iter()
                .filter(|u| a.vars().iter().all(|vp| vp.var != u.var))
                .map(|u| (u.var, u.power)),
        ),
    )
}

/// Compare monomials under an order, as `Ordering` (re-exported helper).
#[must_use]
pub fn cmp_monomials(order: MonomialOrder, a: &Monomial, b: &Monomial) -> Ordering {
    order.compare(a, b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

    fn ctx() -> FieldCtx {
        FieldCtx::new(BigUint::from(97u32)).expect("prime")
    }

    fn mono(vars: &[(u32, u32)]) -> Monomial {
        Monomial::from_powers(vars.iter().map(|&(v, p)| (v, p)))
    }

    fn term_poly(f: &FieldCtx, v: i64, m: Monomial) -> MPoly {
        let mut p = MPoly::zero();
        p.add_term(f, m, &f.from_bigint(&num_bigint::BigInt::from(v)));
        p
    }

    #[test]
    fn add_cancels_and_removes() {
        let f = ctx();
        let mut p = MPoly::zero();
        p.add_term(&f, mono(&[(0, 1)]), &f.from_biguint(&BigUint::from(5u8)));
        p.add_term(&f, mono(&[(0, 1)]), &f.from_biguint(&BigUint::from(92u8)));
        assert!(p.is_zero(), "5 + 92 = 0 mod 97 removes the term");
    }

    #[test]
    fn mul_reduces_mod_p() {
        let f = ctx();
        let a = term_poly(&f, 50, mono(&[(0, 1)]));
        let b = term_poly(&f, 2, mono(&[(1, 1)]));
        let c = a.mul(&f, &b);
        // 50*2 = 100 = 3 mod 97
        assert_eq!(
            c.sorted_terms(MonomialOrder::GrLex),
            vec![(mono(&[(0, 1), (1, 1)]), f.from_biguint(&BigUint::from(3u8)))]
        );
    }

    #[test]
    fn distributivity_over_add() {
        let f = ctx();
        let x = term_poly(&f, 1, mono(&[(0, 1)]));
        let y = term_poly(&f, 1, mono(&[(1, 1)]));
        let two = term_poly(&f, 2, Monomial::unit());
        let lhs = x.add(&f, &y).mul(&f, &two);
        let rhs = x.mul(&f, &two).add(&f, &y.mul(&f, &two));
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn leading_monomial_under_orders() {
        let f = ctx();
        let mut p = MPoly::zero();
        p.add_term(&f, mono(&[(0, 3)]), &f.one());
        p.add_term(&f, mono(&[(1, 1), (0, 1)]), &f.one());
        p.add_term(&f, mono(&[(1, 2)]), &f.one());
        // grevlex: x^3 vs x y vs y^2 — all degree-incomparable pairs? x^3
        // is degree 3, the others 2 → x^3 leads in graded orders.
        assert_eq!(p.lm(MonomialOrder::GRevLex), Some(mono(&[(0, 3)])));
        assert_eq!(p.lm(MonomialOrder::GrLex), Some(mono(&[(0, 3)])));
    }

    #[test]
    fn monomial_arithmetic() {
        let a = mono(&[(0, 2), (1, 1)]);
        let b = mono(&[(0, 1), (2, 3)]);
        let prod = a.mul(&b);
        assert_eq!(prod, mono(&[(0, 3), (1, 1), (2, 3)]));
        assert!(monomial_divides(&a, &mono(&[(0, 1)])));
        assert!(!monomial_divides(&a, &mono(&[(0, 3)])));
        assert_eq!(
            monomial_div(&prod, &b),
            Some(mono(&[(0, 2), (1, 1)])),
            "prod / b = a"
        );
        assert_eq!(monomial_lcm(&a, &b), mono(&[(0, 2), (1, 1), (2, 3)]));
    }

    #[test]
    fn eval_var_and_all() {
        let f = ctx();
        // p = 3x^2y + 2x + 1
        let mut p = MPoly::zero();
        p.add_term(
            &f,
            mono(&[(0, 2), (1, 1)]),
            &f.from_biguint(&BigUint::from(3u8)),
        );
        p.add_term(&f, mono(&[(0, 1)]), &f.from_biguint(&BigUint::from(2u8)));
        p.add_term(&f, Monomial::unit(), &f.one());
        // x := 5 → 75y + 11
        let ev = p.eval_var(&f, 0, &f.from_biguint(&BigUint::from(5u8)));
        assert_eq!(ev.n_terms(), 2);
        // full assignment x=5, y=6: 75*6 + 11 = 461 = 461 - 4*97 = 73
        let mut assignment = FxHashMap::default();
        assignment.insert(0u32, f.from_biguint(&BigUint::from(5u8)));
        assignment.insert(1u32, f.from_biguint(&BigUint::from(6u8)));
        assert_eq!(
            p.eval_all(&f, &assignment),
            f.from_biguint(&BigUint::from(73u8))
        );
    }

    #[test]
    fn monic_normalizes_leading_coefficient() {
        let f = ctx();
        let mut p = MPoly::zero();
        p.add_term(&f, mono(&[(0, 2)]), &f.from_biguint(&BigUint::from(5u8)));
        p.add_term(&f, mono(&[(0, 1)]), &f.from_biguint(&BigUint::from(3u8)));
        let m = p.monic(&f, MonomialOrder::GrLex);
        assert_eq!(
            m.lc(MonomialOrder::GrLex),
            Some(&f.one()),
            "monic leading coefficient"
        );
        // and the value is preserved up to the unit 5^{-1}
        let inv5 = f
            .inv(&f.from_biguint(&BigUint::from(5u8)))
            .expect("5 invertible");
        assert_eq!(m, p.scale(&f, &inv5));
    }
}
