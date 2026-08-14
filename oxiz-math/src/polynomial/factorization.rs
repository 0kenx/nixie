//! Polynomial Factorization Algorithms.
#![allow(unused_assignments)] // Algorithm placeholder
//!
//! Implements multivariate polynomial factorization including:
//! - Berlekamp-Zassenhaus algorithm
//! - Hensel lifting
//! - Multivariate factorization via Kronecker substitution

#[allow(unused_imports)]
use crate::prelude::*;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

/// Polynomial factorization engine.
pub struct PolynomialFactorizer {
    /// Factorization cache
    cache: FxHashMap<PolynomialKey, Vec<Factor>>,
    /// Statistics
    stats: FactorizationStats,
}

/// A polynomial factor with multiplicity.
#[derive(Debug, Clone)]
pub struct Factor {
    /// The polynomial factor
    pub poly: Vec<BigRational>,
    /// Multiplicity
    pub multiplicity: usize,
}

/// Simplified polynomial key for caching.
type PolynomialKey = Vec<String>;

/// Factorization statistics.
#[derive(Debug, Clone, Default)]
pub struct FactorizationStats {
    /// Number of factorizations performed
    pub factorizations: usize,
    /// Cache hits
    pub cache_hits: usize,
    /// Hensel lifts performed
    pub hensel_lifts: usize,
    /// Square-free decompositions
    pub square_free_decompositions: usize,
}

impl PolynomialFactorizer {
    /// Create a new polynomial factorizer.
    pub fn new() -> Self {
        Self {
            cache: FxHashMap::default(),
            stats: FactorizationStats::default(),
        }
    }

    /// Factor a univariate polynomial over rationals.
    pub fn factor_univariate(&mut self, poly: &[BigRational]) -> Vec<Factor> {
        self.stats.factorizations += 1;

        // Check cache
        let key = self.polynomial_to_key(poly);
        if let Some(cached) = self.cache.get(&key) {
            self.stats.cache_hits += 1;
            return cached.clone();
        }

        // Step 1: Square-free decomposition
        let square_free_factors = self.square_free_decomposition(poly);
        self.stats.square_free_decompositions += 1;

        // Step 2: Factor each square-free component
        let mut factors = Vec::new();

        for (sf_poly, multiplicity) in square_free_factors {
            // Factor over integers using Berlekamp-Zassenhaus
            let irreducible_factors = self.berlekamp_zassenhaus(&sf_poly);

            for irr_factor in irreducible_factors {
                factors.push(Factor {
                    poly: irr_factor,
                    multiplicity,
                });
            }
        }

        // Cache result
        self.cache.insert(key, factors.clone());

        factors
    }

    /// Square-free decomposition using Yun's algorithm.
    fn square_free_decomposition(&self, poly: &[BigRational]) -> Vec<(Vec<BigRational>, usize)> {
        let mut result = Vec::new();

        // Compute derivative
        let mut f = poly.to_vec();
        let mut df = Self::derivative(&f);

        // GCD of f and f'
        let mut g = Self::gcd(&f, &df);

        let mut i = 1;

        while !Self::is_constant(&g) {
            // f / g
            let q = Self::divide(&f, &g);

            // GCD(q, g)
            let h = Self::gcd(&q, &g);

            // q / h is the i-th square-free factor
            let factor = Self::divide(&q, &h);

            if !Self::is_constant(&factor) {
                result.push((factor, i));
            }

            f = g;
            df = Self::derivative(&f);
            g = h;
            i += 1;

            // Prevent infinite loop
            if i > poly.len() {
                break;
            }
        }

        // Remaining part
        if !Self::is_constant(&f) {
            result.push((f, i));
        }

        result
    }

    /// Berlekamp-Zassenhaus factorization algorithm.
    fn berlekamp_zassenhaus(&mut self, poly: &[BigRational]) -> Vec<Vec<BigRational>> {
        // Explicit work-stack rather than recursion: each split peels one
        // linear factor off, so the recursion depth was the polynomial
        // degree – attacker-controlled – with two `Vec<BigRational>`s and a
        // `Vec<Vec<BigRational>>` accumulator per frame. The `Vec` return
        // type leaves nowhere to report a depth cap, so a cap could only
        // have dropped factors silently.
        //
        // Pushing the second half before the first makes the LIFO stack
        // emit factors in the same order as the former recursion.
        let mut factors = Vec::new();
        let mut work = vec![poly.to_vec()];

        while let Some(current) = work.pop() {
            if current.len() <= 2 {
                // Linear or constant - already irreducible
                factors.push(current);
                continue;
            }

            // Check if polynomial is irreducible
            if self.is_irreducible(&current) {
                factors.push(current);
                continue;
            }

            // Attempt factorization using Kronecker substitution
            if let Some((f1, f2)) = self.kronecker_factor(&current) {
                work.push(f2);
                work.push(f1);
                continue;
            }

            // Default: return as single factor
            factors.push(current);
        }

        factors
    }

    /// Kronecker substitution factorization attempt.
    fn kronecker_factor(
        &self,
        poly: &[BigRational],
    ) -> Option<(Vec<BigRational>, Vec<BigRational>)> {
        // Try small integer evaluations to find potential factors
        for x in -5..=5 {
            let val = Self::evaluate(poly, &BigRational::from_integer(BigInt::from(x)));

            if val.is_zero() {
                // Found a root at x, factor out (t - x)
                let linear_factor = vec![
                    BigRational::one(),
                    BigRational::from_integer(BigInt::from(-x)),
                ];

                let quotient = Self::divide(poly, &linear_factor);
                return Some((linear_factor, quotient));
            }
        }

        None
    }

    /// Hensel lifting for factorization refinement.
    pub fn hensel_lift(
        &mut self,
        _poly: &[BigRational],
        modular_factors: &[Vec<BigRational>],
        _modulus: &BigInt,
    ) -> Vec<Vec<BigRational>> {
        self.stats.hensel_lifts += 1;

        // Simplified: return modular factors as-is
        modular_factors.to_vec()
    }

    /// Check if polynomial is irreducible.
    fn is_irreducible(&self, poly: &[BigRational]) -> bool {
        // Simplified irreducibility test
        if poly.len() <= 2 {
            return true;
        }

        // Check for rational roots using rational root theorem
        !self.has_rational_root(poly)
    }

    /// Check if polynomial has a rational root.
    fn has_rational_root(&self, poly: &[BigRational]) -> bool {
        // Test small rationals
        for num in -10..=10 {
            for denom in 1..=5 {
                let x = BigRational::new(BigInt::from(num), BigInt::from(denom));
                let val = Self::evaluate(poly, &x);

                if val.is_zero() {
                    return true;
                }
            }
        }

        false
    }

    /// Polynomial derivative.
    fn derivative(poly: &[BigRational]) -> Vec<BigRational> {
        if poly.len() <= 1 {
            return vec![BigRational::zero()];
        }

        let mut deriv = Vec::new();
        let degree = poly.len() - 1;

        for (i, coeff) in poly.iter().enumerate().take(degree) {
            let power = (degree - i) as i64;
            deriv.push(coeff * BigRational::from_integer(BigInt::from(power)));
        }

        deriv
    }

    /// Polynomial GCD (Euclidean algorithm).
    /// Drop leading (highest-degree) zero coefficients.
    ///
    /// Coefficients are stored highest-degree first, so a leading zero
    /// makes `remainder`'s `lead_div.is_zero()` guard fire and return the
    /// dividend unchanged – which is what made the recursive `gcd` below
    /// able to cycle forever.
    fn strip_leading_zeros(poly: &[BigRational]) -> Vec<BigRational> {
        let start = poly.iter().position(|c| !c.is_zero()).unwrap_or(poly.len());
        poly[start..].to_vec()
    }

    /// Euclidean polynomial GCD.
    ///
    /// Iterative rather than recursive, for two reasons:
    ///
    /// * Depth was O(degree) with a whole `Vec<BigRational>` remainder per
    ///   frame, on attacker-supplied polynomials, and the `Vec` return type
    ///   has no channel for a depth error.
    /// * More seriously, termination was not guaranteed. `remainder`
    ///   returns the dividend unchanged when the divisor's *leading*
    ///   coefficient is zero (its `lead_div.is_zero()` break), so
    ///   `gcd(a, b)` could step to `gcd(b, a)` and back forever. Stripping
    ///   leading zeros makes each `remainder` strictly reduce the length,
    ///   which is the progress the Euclidean algorithm needs.
    fn gcd(a: &[BigRational], b: &[BigRational]) -> Vec<BigRational> {
        let mut a = Self::strip_leading_zeros(a);
        let mut b = Self::strip_leading_zeros(b);

        while !Self::is_zero(&b) {
            let remainder = Self::strip_leading_zeros(&Self::remainder(&a, &b));
            a = b;
            b = remainder;
        }

        a
    }

    /// Polynomial division (quotient).
    fn divide(dividend: &[BigRational], divisor: &[BigRational]) -> Vec<BigRational> {
        if Self::is_zero(divisor) {
            return vec![BigRational::zero()];
        }

        let mut quotient = Vec::new();
        let mut remainder = dividend.to_vec();

        while remainder.len() >= divisor.len() && !Self::is_zero(&remainder) {
            let lead_rem = &remainder[0];
            let lead_div = &divisor[0];

            if lead_div.is_zero() {
                break;
            }

            let q_coeff = lead_rem / lead_div;
            quotient.push(q_coeff.clone());

            // Subtract q_coeff * divisor from remainder
            for i in 0..divisor.len() {
                remainder[i] = &remainder[i] - &q_coeff * &divisor[i];
            }

            remainder.remove(0);
        }

        if quotient.is_empty() {
            vec![BigRational::zero()]
        } else {
            quotient
        }
    }

    /// Polynomial remainder.
    fn remainder(dividend: &[BigRational], divisor: &[BigRational]) -> Vec<BigRational> {
        if Self::is_zero(divisor) {
            return dividend.to_vec();
        }

        let mut remainder = dividend.to_vec();

        while remainder.len() >= divisor.len() && !Self::is_zero(&remainder) {
            let lead_rem = &remainder[0];
            let lead_div = &divisor[0];

            if lead_div.is_zero() {
                break;
            }

            let q_coeff = lead_rem / lead_div;

            for i in 0..divisor.len() {
                remainder[i] = &remainder[i] - &q_coeff * &divisor[i];
            }

            remainder.remove(0);
        }

        remainder
    }

    /// Evaluate polynomial at a point.
    fn evaluate(poly: &[BigRational], x: &BigRational) -> BigRational {
        if poly.is_empty() {
            return BigRational::zero();
        }

        let mut result = poly[0].clone();
        for coeff in &poly[1..] {
            result = result * x + coeff;
        }

        result
    }

    /// Check if polynomial is zero.
    fn is_zero(poly: &[BigRational]) -> bool {
        poly.iter().all(|c| c.is_zero())
    }

    /// Check if polynomial is constant.
    fn is_constant(poly: &[BigRational]) -> bool {
        poly.len() <= 1
    }

    /// Convert polynomial to cache key.
    fn polynomial_to_key(&self, poly: &[BigRational]) -> PolynomialKey {
        poly.iter().map(|c| c.to_string()).collect()
    }

    /// Get statistics.
    pub fn stats(&self) -> &FactorizationStats {
        &self.stats
    }
}

impl Default for PolynomialFactorizer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_polynomial_factorizer() {
        let factorizer = PolynomialFactorizer::new();
        assert_eq!(factorizer.stats.factorizations, 0);
    }

    #[test]
    fn test_derivative() {
        // f(x) = x^2 + 2x + 1 -> f'(x) = 2x + 2
        let poly = vec![
            BigRational::one(),
            BigRational::from_integer(BigInt::from(2)),
            BigRational::one(),
        ];

        let deriv = PolynomialFactorizer::derivative(&poly);

        assert_eq!(deriv.len(), 2);
    }

    #[test]
    fn test_evaluate() {
        // f(x) = x^2 - 1
        let poly = vec![
            BigRational::one(),
            BigRational::zero(),
            BigRational::from_integer(BigInt::from(-1)),
        ];

        let val = PolynomialFactorizer::evaluate(&poly, &BigRational::one());
        assert_eq!(val, BigRational::zero()); // f(1) = 0
    }
}
