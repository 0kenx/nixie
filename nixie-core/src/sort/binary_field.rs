//! Polynomial-basis binary fields, with a checked irreducible modulus.
//!
//! Bit i is the coefficient of X^i, not an integer residue. Irreducibility
//! uses HAC Algorithm 4.69 (Ben-Or): gcd(f, X^(2^i)-X)=1 for
//! 1 <= i <= floor(deg(f)/2). Compare NTL GF2XFactoring::IterIrredTest.
//! Arithmetic is carryless polynomial arithmetic followed by long division.

use num_bigint::BigUint;
use num_traits::{One, Zero};

/// `F_2[X]/(f)`, with monic irreducible f of degree 2..=256.
/// Immutable private parameters ensure callers cannot bypass validation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryField {
    polynomial: BigUint,
    degree: u32,
}

impl BinaryField {
    /// Validate a binary polynomial, including its leading coefficient.
    /// The degree cap bounds the deterministic construction work.
    pub fn new(polynomial: BigUint) -> Result<Self, super::field::FieldError> {
        let bits = polynomial.bits();
        let invalid = |reason: &str| super::field::FieldError::NotAField {
            order: polynomial.to_string(),
            reason: reason.to_owned(),
        };
        if !(3..=257).contains(&bits) {
            return Err(invalid(
                "binary defining polynomial must have degree 2..=256",
            ));
        }
        let degree = (bits - 1) as u32;
        let mut power = BigUint::from(2u8); // X
        for _ in 1..=degree / 2 {
            power = remainder(product(&power, &power), &polynomial);
            let mut a = polynomial.clone();
            let mut b = &power ^ BigUint::from(2u8);
            while !b.is_zero() {
                let r = remainder(a, &b);
                a = b;
                b = r;
            }
            if !a.is_one() {
                return Err(invalid("binary defining polynomial is reducible"));
            }
        }
        Ok(Self { polynomial, degree })
    }

    /// The complete defining polynomial, including its monic leading term.
    #[must_use]
    pub fn polynomial(&self) -> &BigUint {
        &self.polynomial
    }

    /// Extension degree over the prime base field F_2.
    #[must_use]
    pub fn degree(&self) -> u32 {
        self.degree
    }

    /// Cardinality (distinct from characteristic two).
    #[must_use]
    pub fn order(&self) -> BigUint {
        BigUint::one() << self.degree
    }

    /// Whether a polynomial-basis encoding is canonical.
    #[must_use]
    pub fn contains(&self, a: &BigUint) -> bool {
        a.bits() <= u64::from(self.degree)
    }

    /// Reduce an arbitrary binary polynomial to its canonical representative.
    #[must_use]
    pub fn reduce(&self, a: BigUint) -> BigUint {
        remainder(a, &self.polynomial)
    }

    /// Addition of canonical elements; rejects out-of-field encodings.
    #[must_use]
    pub fn add(&self, a: &BigUint, b: &BigUint) -> Option<BigUint> {
        (self.contains(a) && self.contains(b)).then(|| a ^ b)
    }

    /// Multiplication of canonical elements; never integer multiplication.
    #[must_use]
    pub fn mul(&self, a: &BigUint, b: &BigUint) -> Option<BigUint> {
        (self.contains(a) && self.contains(b)).then(|| self.reduce(product(a, b)))
    }

    /// Exact exponentiation by square-and-multiply.
    #[must_use]
    pub fn pow(&self, a: &BigUint, exponent: &BigUint) -> Option<BigUint> {
        if !self.contains(a) {
            return None;
        }
        let mut result = BigUint::one();
        let mut base = a.clone();
        for i in 0..exponent.bits() {
            if exponent.bit(i) {
                result = self.mul(&result, &base)?;
            }
            base = self.mul(&base, &base)?;
        }
        Some(result)
    }

    /// Inversion by a^(q-2); zero and noncanonical encodings have no inverse.
    #[must_use]
    pub fn inverse(&self, a: &BigUint) -> Option<BigUint> {
        if a.is_zero() {
            return None;
        }
        self.pow(a, &(self.order() - 2u8))
    }
}

fn product(a: &BigUint, b: &BigUint) -> BigUint {
    let mut out = BigUint::zero();
    for i in 0..b.bits() {
        if b.bit(i) {
            out ^= a << i;
        }
    }
    out
}

// Internal callers establish a nonzero divisor. Each step decreases degree.
fn remainder(mut a: BigUint, divisor: &BigUint) -> BigUint {
    debug_assert!(!divisor.is_zero());
    while a.bits() >= divisor.bits() {
        let shift = a.bits() - divisor.bits();
        a ^= divisor << shift;
    }
    a
}
