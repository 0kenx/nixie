//! Dense univariate polynomials over 𝔽_p (`docs/FF_THEORY_DESIGN.md` §4.2).
//!
//! Coefficients are Montgomery-form [`Limbs`] relative to one [`FieldCtx`];
//! the vector is little-endian (`coeffs[i]` multiplies `x^i`) and the zero
//! polynomial is the empty vector. Degrees stay small in this application
//! (circuit-derived systems), so schoolbook multiply with a Karatsuba
//! crossover is the right shape; NTT is a later optimization with a
//! benchmark attached, not a design premise.
//!
//! `p = 2` has no [`FieldCtx`] (Montgomery form needs an odd modulus); the
//! modules above this one handle `𝔽_2` through an exact `BigUint`-backed
//! path where it matters (root finding's trace map). These polynomials are
//! built for odd primes.

use super::field::{FieldCtx, Limbs};
use num_bigint::BigUint;
use num_traits::Zero;

/// A dense univariate polynomial over one 𝔽_p.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UniPoly {
    /// Little-endian coefficients in Montgomery form; no trailing zeros.
    coeffs: Vec<Limbs>,
}

impl UniPoly {
    /// The zero polynomial.
    #[must_use]
    pub fn zero() -> Self {
        Self { coeffs: Vec::new() }
    }

    /// Build from little-endian coefficients, trimming high zeros.
    #[must_use]
    pub fn from_coeffs(coeffs: Vec<Limbs>) -> Self {
        let mut p = Self { coeffs };
        p.trim();
        p
    }

    /// The constant `c`.
    #[must_use]
    pub fn constant(f: &FieldCtx, c: &Limbs) -> Self {
        if f.is_zero(c) {
            Self::zero()
        } else {
            Self {
                coeffs: vec![c.clone()],
            }
        }
    }

    fn trim(&mut self) {
        while self.coeffs.last().is_some_and(is_zero_limb) {
            self.coeffs.pop();
        }
    }

    /// Whether this is the zero polynomial.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }

    /// The degree; the zero polynomial has degree `None` (it has no
    /// monomial of highest degree — reporting `0` would confuse it with
    /// the nonzero constant).
    #[must_use]
    pub fn degree(&self) -> Option<usize> {
        if self.coeffs.is_empty() {
            None
        } else {
            Some(self.coeffs.len() - 1)
        }
    }

    /// The leading coefficient (Montgomery form); `None` for zero.
    #[must_use]
    pub fn lc(&self) -> Option<&Limbs> {
        self.coeffs.last()
    }

    /// Coefficient slice, little-endian.
    #[must_use]
    pub fn coeffs(&self) -> &[Limbs] {
        &self.coeffs
    }

    /// Evaluate at `x` (Horner, Montgomery-exact).
    #[must_use]
    pub fn eval(&self, f: &FieldCtx, x: &Limbs) -> Limbs {
        let mut acc = self.zero_limb(f);
        for c in self.coeffs.iter().rev() {
            acc = f.add(&f.mul(&acc, x), c);
        }
        acc
    }

    fn zero_limb(&self, f: &FieldCtx) -> Limbs {
        f.zero()
    }

    /// Polynomial addition.
    #[must_use]
    pub fn add(&self, f: &FieldCtx, other: &Self) -> Self {
        let n = self.coeffs.len().max(other.coeffs.len());
        let mut coeffs = Vec::with_capacity(n);
        for i in 0..n {
            let a = self.coeffs.get(i);
            let b = other.coeffs.get(i);
            match (a, b) {
                (Some(a), Some(b)) => coeffs.push(f.add(a, b)),
                (Some(a), None) => coeffs.push(a.clone()),
                (None, Some(b)) => coeffs.push(b.clone()),
                (None, None) => unreachable!("loop bound is the max"),
            }
        }
        Self::from_coeffs(coeffs)
    }

    /// Polynomial negation.
    #[must_use]
    pub fn neg(&self, f: &FieldCtx) -> Self {
        Self::from_coeffs(self.coeffs.iter().map(|c| f.neg(c)).collect())
    }

    /// Polynomial subtraction.
    #[must_use]
    pub fn sub(&self, f: &FieldCtx, other: &Self) -> Self {
        self.add(f, &other.neg(f))
    }

    /// Scalar multiplication.
    #[must_use]
    pub fn scale(&self, f: &FieldCtx, s: &Limbs) -> Self {
        if f.is_zero(s) {
            return Self::zero();
        }
        Self::from_coeffs(self.coeffs.iter().map(|c| f.mul(c, s)).collect())
    }

    /// Monomial multiplication by `x^k`.
    #[must_use]
    pub fn shift(&self, k: usize) -> Self {
        if self.is_zero() {
            return Self::zero();
        }
        let mut coeffs = vec![self.zero_limb_placeholder(); k];
        coeffs.extend(self.coeffs.iter().cloned());
        Self { coeffs }
    }

    fn zero_limb_placeholder(&self) -> Limbs {
        // Width comes from the stored limbs; safe because `shift` is only
        // called on a nonzero polynomial (guarded above).
        smallvec::smallvec![0u64; self.coeffs[0].len()]
    }

    /// Schoolbook multiplication (Karatsuba above the crossover is a
    /// measured TODO; degrees here are small).
    #[must_use]
    pub fn mul(&self, f: &FieldCtx, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        let mut coeffs = vec![f.zero(); self.coeffs.len() + other.coeffs.len() - 1];
        for (i, a) in self.coeffs.iter().enumerate() {
            for (j, b) in other.coeffs.iter().enumerate() {
                let prod = f.mul(a, b);
                let sum = f.add(&coeffs[i + j], &prod);
                coeffs[i + j] = sum;
            }
        }
        Self::from_coeffs(coeffs)
    }

    /// Monic normalization: divide by the leading coefficient. The zero
    /// polynomial is returned unchanged (it has no leading coefficient to
    /// normalize by).
    #[must_use]
    pub fn monic(&self, f: &FieldCtx) -> Self {
        match self.lc() {
            None => Self::zero(),
            Some(lc) => {
                let inv = f.inv(lc);
                match inv {
                    Some(inv) => self.scale(f, &inv),
                    None => Self::zero(), // lc = 0 impossible after trim
                }
            }
        }
    }

    /// Polynomial division with remainder: `(self) = q·(divisor) + r`,
    /// `deg r < deg divisor`. Panics never; dividing by zero returns
    /// `None` (an honest refusal — no quotient exists).
    #[must_use]
    pub fn divrem(&self, f: &FieldCtx, divisor: &Self) -> Option<(Self, Self)> {
        let d = divisor.degree()?;
        let mut r = self.clone();
        let mut q = vec![f.zero(); self.coeffs.len()];
        let lc_inv = f.inv(divisor.lc()?)?;
        while let Some(dr) = r.degree() {
            if dr < d {
                break;
            }
            let factor = f.mul(r.lc()?, &lc_inv);
            let shift = dr - d;
            q[shift] = factor.clone();
            // r -= factor * divisor * x^shift
            let mut sub_coeffs = vec![f.zero(); shift + divisor.coeffs.len()];
            for (i, c) in divisor.coeffs.iter().enumerate() {
                sub_coeffs[shift + i] = f.mul(c, &factor);
            }
            let sub = Self::from_coeffs(sub_coeffs);
            r = r.sub(f, &sub);
        }
        q.truncate(q.len().min(self.coeffs.len().max(1)));
        Some((Self::from_coeffs(q), r))
    }

    /// Euclidean GCD (both polynomials monic-normalized on output; the
    /// GCD of two polynomials is defined up to a unit).
    #[must_use]
    pub fn gcd(&self, f: &FieldCtx, other: &Self) -> Self {
        let mut a = self.clone();
        let mut b = other.clone();
        while !b.is_zero() {
            let Some((_, r)) = a.divrem(f, &b) else {
                break;
            };
            a = b;
            b = r;
        }
        a.monic(f)
    }

    /// `self^e mod m` by repeated squaring in `F[x]/(m)`.
    #[must_use]
    pub fn pow_mod(&self, f: &FieldCtx, e: &BigUint, m: &Self) -> Self {
        let mut result = match m.degree() {
            Some(0) | None => Self::zero(), // quotient ring is trivial
            _ => Self::constant(f, &f.one()),
        };
        if e.is_zero() {
            return result;
        }
        let Some((_, base)) = self.divrem(f, m) else {
            return Self::zero();
        };
        let mut base = base;
        let bits = e.bits();
        for i in 0..bits {
            if e.bit(i) {
                result = result.mul(f, &base).reduce_mod(f, m);
            }
            base = base.mul(f, &base).reduce_mod(f, m);
        }
        result
    }

    /// Reduce modulo `m` (via `divrem`).
    #[must_use]
    pub fn reduce_mod(&self, f: &FieldCtx, m: &Self) -> Self {
        match self.divrem(f, m) {
            Some((_, r)) => r,
            None => self.clone(),
        }
    }

    /// The formal derivative.
    #[must_use]
    pub fn derivative(&self, f: &FieldCtx) -> Self {
        if self.coeffs.len() <= 1 {
            return Self::zero();
        }
        let mut coeffs = Vec::with_capacity(self.coeffs.len() - 1);
        for (i, c) in self.coeffs.iter().enumerate().skip(1) {
            let n = f.from_biguint(&BigUint::from(i as u64));
            coeffs.push(f.mul(c, &n));
        }
        Self::from_coeffs(coeffs)
    }

    /// The squarefree part: the product of the distinct irreducible
    /// factors, computed as `self / gcd(self, self')`. Classic and exact
    /// in characteristic `p` **only when** handled carefully: in
    /// characteristic p a polynomial can have a zero derivative
    /// (`x^p`), and then `gcd(f, f') = f` and the quotient is 1. That
    /// case is *not* an error — it says every root has multiplicity
    /// divisible by p — and the caller (root finding) treats it via the
    /// Frobenius. Here we return the honest quotient, which for `f = g^p`
    /// is `1`.
    #[must_use]
    pub fn squarefree_part(&self, f: &FieldCtx) -> Self {
        let d = self.derivative(f);
        if d.is_zero() {
            return Self::constant(f, &f.one());
        }
        let g = self.gcd(f, &d);
        if g.is_zero() || g.degree() == Some(0) {
            return self.clone();
        }
        self.divrem(f, &g)
            .map_or_else(Self::zero, |(q, _)| q.monic(f))
    }
}

fn is_zero_limb(l: &Limbs) -> bool {
    l.iter().all(|&x| x == 0)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ctx() -> FieldCtx {
        FieldCtx::new(BigUint::from(97u32)).expect("97 is prime")
    }

    fn poly(f: &FieldCtx, ints: &[i64]) -> UniPoly {
        UniPoly::from_coeffs(
            ints.iter()
                .map(|&v| f.from_bigint(&num_bigint::BigInt::from(v)))
                .collect(),
        )
    }

    #[test]
    fn degree_and_trim() {
        let f = ctx();
        assert_eq!(poly(&f, &[]).degree(), None);
        assert_eq!(poly(&f, &[0, 0, 5]).degree(), Some(2));
        assert_eq!(poly(&f, &[1, 2, 0, 0]).degree(), Some(1));
    }

    #[test]
    fn add_sub_mul_round_trip() {
        let f = ctx();
        let a = poly(&f, &[1, 2, 3]);
        let b = poly(&f, &[5, 7]);
        let sum = a.add(&f, &b);
        assert_eq!(sum, poly(&f, &[6, 9, 3]));
        // a - (a + b) = -b, and (a - b) + b = a.
        assert_eq!(a.sub(&f, &sum), poly(&f, &[-5, -7]));
        assert_eq!(a.sub(&f, &b).add(&f, &b), a);
        // (1 + 2x + 3x²)(5 + 7x) = 5 + 17x + 29x² + 21x³  (mod 97)
        assert_eq!(a.mul(&f, &b), poly(&f, &[5, 17, 29, 21]));
    }

    #[test]
    fn divrem_is_exact() {
        let f = ctx();
        let a = poly(&f, &[5, 17, 29, 21]);
        let b = poly(&f, &[5, 7]);
        let (q, r) = a.divrem(&f, &b).expect("b is nonzero");
        assert_eq!(q, poly(&f, &[1, 2, 3]));
        assert!(r.is_zero());
        // A remainder case: x^2 + 1 divided by x + 1 gives x - 1 rem 2.
        let a = poly(&f, &[1, 0, 1]);
        let b = poly(&f, &[1, 1]);
        let (q, r) = a.divrem(&f, &b).expect("nonzero divisor");
        assert_eq!(q, poly(&f, &[96, 1])); // x - 1
        assert_eq!(r, poly(&f, &[2]));
        // Reconstruction identity.
        let rebuilt = q.mul(&f, &b).add(&f, &r);
        assert_eq!(rebuilt.monic(&f), a.monic(&f));
    }

    #[test]
    fn divrem_by_zero_is_refused() {
        let f = ctx();
        let a = poly(&f, &[1, 1]);
        assert!(a.divrem(&f, &UniPoly::zero()).is_none());
    }

    #[test]
    fn gcd_of_coprime_is_one() {
        let f = ctx();
        let a = poly(&f, &[1, 1]); // x + 1
        let b = poly(&f, &[2, 1]); // x + 2
        assert_eq!(a.gcd(&f, &b), UniPoly::constant(&f, &f.one()));
        // (x+1) shares a factor with itself.
        assert_eq!(a.gcd(&f, &a), poly(&f, &[1, 1]).monic(&f));
    }

    #[test]
    fn pow_mod_matches_direct_pow_then_reduce() {
        let f = ctx();
        let base = poly(&f, &[3, 1, 4]); // 3 + x + 4x^2
        let m = poly(&f, &[1, 0, 1, 1]); // 1 + x^2 + x^3
        // e = 13
        let via_mod = base.pow_mod(&f, &BigUint::from(13u32), &m);
        let mut direct = UniPoly::constant(&f, &f.one());
        for _ in 0..13 {
            direct = direct.mul(&f, &base);
        }
        assert_eq!(via_mod, direct.reduce_mod(&f, &m));
    }

    #[test]
    fn derivative_and_squarefree() {
        let f = ctx();
        // (x+1)^2 = x^2 + 2x + 1: squarefree part is x+1.
        let a = poly(&f, &[1, 2, 1]);
        assert_eq!(a.squarefree_part(&f), poly(&f, &[1, 1]));
        // A squarefree polynomial is its own squarefree part.
        let b = poly(&f, &[1, 1, 1]);
        assert_eq!(b.squarefree_part(&f), b.monic(&f));
    }

    #[test]
    fn eval_horner() {
        let f = ctx();
        let a = poly(&f, &[1, 2, 3]);
        let x = f.from_biguint(&BigUint::from(5u32));
        // 1 + 2*5 + 3*25 = 86
        assert_eq!(a.eval(&f, &x), f.from_biguint(&BigUint::from(86u32)));
    }
}
