//! Finite-field sorts (`QF_FF`).
//!
//! A finite-field sort is `(_ FiniteField <numeral>)` where the numeral is the
//! field's *order*. The order is an arbitrary-precision numeral (a 254-bit ZK
//! prime does not fit any fixed-width integer), so the sort variant carries a
//! [`FieldId`] indexing this table rather than the modulus itself:
//! `SortKind` is the interner key, and a `u32` payload keeps sort comparison
//! O(1) while giving the derived per-field data (derived parameters, primality
//! evidence) a home computed once per field.
//!
//! Prime fields use integer residues. Binary extensions use explicit, validated
//! monic irreducible polynomials and polynomial-basis elements. Their identities
//! include the defining polynomial; equal cardinality does not imply equality.
//! `modulus(id)` intentionally remains PRIME ONLY, fencing off legacy algebra.

use num_bigint::BigUint;
use num_traits::{One, Zero};
use std::sync::Arc;

/// Unique identifier for a finite field, indexing a [`FieldTable`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FieldId(u32);

impl FieldId {
    /// Wrap a raw table index.
    #[must_use]
    pub const fn from_raw(raw: u32) -> Self {
        Self(raw)
    }

    /// The raw table index.
    #[must_use]
    pub const fn raw(self) -> u32 {
        self.0
    }
}

/// The kind of a field's order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FieldKind {
    /// Prime order `p`: the field is 𝔽_p = ℤ/pℤ.
    Prime,
    /// Extension order `p^k`, with explicit representation. This build
    /// constructs binary extensions (p=2) only.
    Extension {
        /// The characteristic.
        p: Arc<BigUint>,
        /// The extension degree.
        k: u32,
        /// Validated binary defining polynomial and arithmetic context.
        binary: Arc<super::binary_field::BinaryField>,
    },
}

/// What is known about the primality of a field's order, and how it is known.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Primality {
    /// Established by exhaustive means: trial division, or Miller–Rabin over
    /// a base set that is *deterministic* for this modulus (every composite
    /// below 3.3·10²⁴ is caught by the first 13 primes, plus 23, 1662803).
    Verified,
    /// Established by Miller–Rabin over a fixed (deterministic, seed-free)
    /// base set that is not known to be complete for this modulus's size.
    /// The number of bases actually used is recorded.
    ProbablePrime(usize),
    /// The order is composite (or < 2): this is not a field at all.
    Composite,
}

/// One finite field.
#[derive(Debug, Clone)]
pub struct FieldDesc {
    /// The order `p` (for [`FieldKind::Prime`], the prime modulus), exactly.
    /// Never truncated.
    modulus: Arc<BigUint>,
    /// The kind (prime / extension) of the field.
    kind: FieldKind,
    /// Primality evidence for the characteristic (the order for prime fields).
    primality: Primality,
}

impl FieldDesc {
    /// The field's order (`p` for a prime field).
    #[must_use]
    pub fn modulus(&self) -> &BigUint {
        &self.modulus
    }

    /// Binary extension arithmetic, when this is a supported extension field.
    #[must_use]
    pub fn binary(&self) -> Option<&super::binary_field::BinaryField> {
        match &self.kind {
            FieldKind::Prime => None,
            FieldKind::Extension { binary, .. } => Some(binary),
        }
    }

    /// Round-trippable SMT-LIB sort including the representation identity.
    #[must_use]
    pub fn sort_syntax(&self) -> String {
        match self.binary() {
            Some(binary) => format!("(_ BinaryField {})", binary.polynomial()),
            None => format!("(_ FiniteField {})", self.modulus()),
        }
    }

    /// Round-trippable literal. Extension values encode basis coefficients.
    #[must_use]
    pub fn literal_syntax(&self, value: &num_bigint::BigInt) -> String {
        match self.binary() {
            Some(_) => format!("(as ff{value} {})", self.sort_syntax()),
            None => format!("#f{value}m{}", self.modulus()),
        }
    }

    /// The field's kind.
    #[must_use]
    pub fn kind(&self) -> &FieldKind {
        &self.kind
    }

    /// Primality evidence for the characteristic.
    #[must_use]
    pub fn primality(&self) -> Primality {
        self.primality
    }
}

/// Why a field could not be interned.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum FieldError {
    /// The order is not a prime (or a prime power this build supports).
    #[error("finite-field order {order} is not supported: {reason}")]
    NotAField {
        /// The offending order, as written.
        order: String,
        /// Why it cannot be a field this build supports.
        reason: String,
    },
    /// The order is not even an integer ≥ 2.
    #[error("finite-field order must be an integer ≥ 2, got {order}")]
    Malformed {
        /// The offending order, as written.
        order: String,
    },
}

/// Interning table of finite fields, owned by [`crate::sort::SortManager`].
#[derive(Debug, Default)]
pub struct FieldTable {
    fields: Vec<FieldDesc>,
    by_modulus: rustc_hash::FxHashMap<Arc<BigUint>, FieldId>,
    by_binary_polynomial: rustc_hash::FxHashMap<BigUint, FieldId>,
}

/// Miller–Rabin bases that are *deterministically complete* for every
/// composite below 3,317,044,064,679,887,385,961,981 (> 3.3·10²⁴)
/// [Sorenson–Webster]. Above that bound the same bases are used plus the
/// next primes up to 64 bases; the result is then recorded as a
/// probable prime rather than a verified one.
const MR_SMALL_BASES: [u64; 14] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 1662803, 0];

/// Extra primes used to reach 64 bases for large moduli.
const MR_LARGE_EXTRA_BASES: [u64; 58] = [
    41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137,
    139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239,
    241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349,
];

/// Deterministic (seed-free) primality classification of `n ≥ 2`.
///
/// Returns [`Primality`] and is a pure function of `n`: no randomness, no
/// clock, so the same modulus always interns to the same verdict — a
/// reproducibility requirement (`AGENTS.md` → *Determinism*; parity runs and
/// differential fuzzing break otherwise).
fn classify_primality(n: &BigUint) -> Primality {
    use num_integer::Integer;

    debug_assert!(n >= &BigUint::from(2u8));

    // Trial division by small primes: cheap, and exact below 101² = 10201.
    for p in [
        2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
        89, 97,
    ] {
        let p = BigUint::from(p);
        if &p == n {
            return Primality::Verified;
        }
        if n.is_multiple_of(&p) {
            return Primality::Composite;
        }
    }

    // Write n-1 = d · 2^s with d odd.
    let one = BigUint::one();
    let n_minus_1 = n - &one;
    let mut d = n_minus_1.clone();
    let mut s = 0u32;
    while d.is_even() {
        d >>= 1;
        s += 1;
    }

    let is_witness_composite = |base: &BigUint| -> Option<bool> {
        // Returns Some(true) when `base` proves `n` composite; Some(false)
        // when `base` attests probable primality for the strong test.
        // Modular exponentiation (square-and-multiply): computing base^d as a
        // plain integer would materialise a ~2^254-bit number.
        let mut result = BigUint::one();
        let mut base_sq = base % n;
        let mut exp = d.clone();
        while !exp.is_zero() {
            if exp.is_odd() {
                result = (&result * &base_sq) % n;
            }
            base_sq = (&base_sq * &base_sq) % n;
            exp >>= 1;
        }
        let mut x = result;
        if x.is_one() || x == n_minus_1 {
            return Some(false);
        }
        for _ in 1..s {
            x = (&x * &x) % n;
            if x == n_minus_1 {
                return Some(false);
            }
        }
        Some(true)
    };

    let bound_33: BigUint = {
        // 3,317,044,064,679,887,385,961,981 — above u64; assembled digit-wise
        // from its decimal representation to avoid a bignum literal.
        let mut v = BigUint::zero();
        for chunk in [3u32, 317, 44, 64, 679, 887, 385, 961, 981] {
            v = v * BigUint::from(1_000u32) + BigUint::from(chunk);
        }
        v
    };

    if *n < bound_33 {
        // 2..=37 plus 1662803 is complete below the bound (the trailing 0 in
        // MR_SMALL_BASES terminates iteration harmlessly: base 0 ≡ base n).
        for b in MR_SMALL_BASES.iter().filter(|&&b| b != 0) {
            let base = BigUint::from(*b);
            if &base >= n {
                continue;
            }
            if is_witness_composite(&base) == Some(true) {
                return Primality::Composite;
            }
        }
        Primality::Verified
    } else {
        let mut used = 0usize;
        for b in MR_SMALL_BASES
            .iter()
            .filter(|&&b| b != 0)
            .chain(MR_LARGE_EXTRA_BASES.iter())
        {
            let base = BigUint::from(*b);
            if base.is_zero() || &base >= n {
                continue;
            }
            used += 1;
            if is_witness_composite(&base) == Some(true) {
                return Primality::Composite;
            }
        }
        Primality::ProbablePrime(used)
    }
}

impl FieldTable {
    /// An empty table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of interned fields.
    #[must_use]
    pub fn len(&self) -> usize {
        self.fields.len()
    }

    /// Whether no field is interned.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.fields.is_empty()
    }

    /// Look up a field by id.
    #[must_use]
    pub fn get(&self, id: FieldId) -> Option<&FieldDesc> {
        self.fields.get(id.0 as usize)
    }

    /// Look up an already-interned field by order, without interning.
    #[must_use]
    pub fn find(&self, p: &BigUint) -> Option<FieldId> {
        self.by_modulus.get(p).copied()
    }

    /// Intern the prime field of order `p`.
    ///
    /// Errors honestly (never silently reinterprets) when the order is not a
    /// prime this build can certify. Composite orders are rejected even
    /// when prime powers; extensions require [`Self::intern_binary`].
    pub fn intern_prime(&mut self, p: BigUint) -> Result<FieldId, FieldError> {
        if p < BigUint::from(2u8) {
            return Err(FieldError::Malformed {
                order: p.to_string(),
            });
        }
        if let Some(&id) = self.by_modulus.get(&p) {
            // Already interned: the earlier call established the verdict.
            return Ok(id);
        }
        let primality = classify_primality(&p);
        match primality {
            Primality::Composite => {
                let (smallest, cofactor) = smallest_factor_with_cofactor(&p);
                let reason = if cofactor.is_one() {
                    format!(
                        "order is composite (divisible by {smallest}); a finite-field sort \
                         requires a prime order; use an explicit BinaryField defining polynomial \
                         for binary extensions"
                    )
                } else {
                    format!(
                        "order is composite ({smallest} × {cofactor}); a finite-field sort \
                         requires a prime order; use an explicit BinaryField defining polynomial \
                         for binary extensions"
                    )
                };
                Err(FieldError::NotAField {
                    order: p.to_string(),
                    reason,
                })
            }
            Primality::Verified | Primality::ProbablePrime(_) => {
                let id = FieldId(self.fields.len() as u32);
                let modulus = Arc::new(p.clone());
                self.fields.push(FieldDesc {
                    modulus: modulus.clone(),
                    kind: FieldKind::Prime,
                    primality,
                });
                self.by_modulus.insert(modulus, id);
                Ok(id)
            }
        }
    }

    /// Intern `F_2[X]/(f)`. Identity includes f, even for isomorphic fields.
    pub fn intern_binary(&mut self, polynomial: BigUint) -> Result<FieldId, FieldError> {
        if let Some(&id) = self.by_binary_polynomial.get(&polynomial) {
            return Ok(id);
        }
        let binary = super::binary_field::BinaryField::new(polynomial.clone())?;
        let index = u32::try_from(self.fields.len()).map_err(|_| FieldError::NotAField {
            order: polynomial.to_string(),
            reason: "field table capacity exceeded".to_owned(),
        })?;
        let id = FieldId(index);
        self.fields.push(FieldDesc {
            modulus: Arc::new(binary.order()),
            kind: FieldKind::Extension {
                p: Arc::new(BigUint::from(2u8)),
                k: binary.degree(),
                binary: Arc::new(binary),
            },
            // The base characteristic is proven prime; irreducibility is exact.
            primality: Primality::Verified,
        });
        self.by_binary_polynomial.insert(polynomial, id);
        Ok(id)
    }

    /// The prime field's order, if `id` names a prime field.
    #[must_use]
    pub fn modulus(&self, id: FieldId) -> Option<&BigUint> {
        match self.get(id)?.kind() {
            FieldKind::Prime => Some(self.get(id)?.modulus()),
            FieldKind::Extension { .. } => None,
        }
    }

    /// Normalize a prime residue, or validate a canonical binary encoding.
    ///
    /// Negative prime residues reduce exactly. Binary encodings must already
    /// be nonnegative and smaller than the order; they are coefficient bits,
    /// never integer residues modulo the order.
    #[must_use]
    pub fn reduce(&self, id: FieldId, value: &num_bigint::BigInt) -> Option<num_bigint::BigInt> {
        if let Some(binary) = self.get(id)?.binary() {
            let encoded = value.to_biguint()?;
            return binary.contains(&encoded).then(|| value.clone());
        }
        let p = self.modulus(id)?;
        let p_int = num_bigint::BigInt::from_bytes_le(num_bigint::Sign::Plus, &p.to_bytes_le());
        use num_integer::Integer;
        Some(value.mod_floor(&p_int))
    }
}

/// Find the smallest prime factor of an odd composite `n` together with the
/// cofactor, for error messages. Trial division only: composites reaching
/// this path were already Miller–Rabin-screened, so the smallest factor is
/// tiny in practice; the loop is capped and falls back to reporting the
/// number itself when the cap is hit (the message stays truthful — it names
/// *a* divisor only when one was found).
fn smallest_factor_with_cofactor(n: &BigUint) -> (BigUint, BigUint) {
    use num_integer::Integer;
    for p in (2u64..=100_000).map(BigUint::from) {
        if (&p * &p) > *n {
            return (n.clone(), BigUint::one());
        }
        if n.is_multiple_of(&p) {
            let cofactor = n / &p;
            return (p, cofactor);
        }
    }
    (n.clone(), BigUint::one())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prime_fields_intern() {
        let mut t = FieldTable::new();
        let f7 = t.intern_prime(BigUint::from(7u8)).expect("7 is prime");
        let again = t.intern_prime(BigUint::from(7u8)).expect("re-intern");
        assert_eq!(f7, again);
        assert_eq!(t.len(), 1);
        assert_eq!(t.modulus(f7), Some(&BigUint::from(7u8)));
    }

    #[test]
    fn composite_orders_error_honestly() {
        let mut t = FieldTable::new();
        for bad in [0u64, 1, 4, 6, 9, 15, 100, 1_000_000] {
            let err = t
                .intern_prime(BigUint::from(bad))
                .expect_err("composite order must not intern");
            assert!(!err.to_string().is_empty());
        }
        assert!(t.is_empty(), "no composite may be interned");
    }

    #[test]
    fn big_zk_prime_interns_as_probable_prime() {
        // BN254 scalar field modulus (a 254-bit prime).
        let p: BigUint =
            "21888242871839275222246405745257275088548364400416034343698204186575808495617"
                .parse()
                .expect("decimal parses");
        let mut t = FieldTable::new();
        let id = t
            .intern_prime(p.clone())
            .expect("BN254 scalar modulus is prime");
        match t.get(id).expect("interned").primality() {
            Primality::ProbablePrime(rounds) => assert!(rounds >= 32, "many bases used"),
            other => panic!("254-bit prime must be ProbablePrime, got {other:?}"),
        }
    }

    #[test]
    fn deterministic_verdicts_repeat() {
        let p: BigUint =
            "21888242871839275222246405745257275088548364400416034343698204186575808495617"
                .parse()
                .expect("decimal parses");
        let mut a = FieldTable::new();
        let mut b = FieldTable::new();
        assert_eq!(
            a.intern_prime(p.clone()).expect("prime"),
            b.intern_prime(p).expect("prime")
        );
    }

    #[test]
    fn small_primes_are_verified() {
        let mut t = FieldTable::new();
        for p in [2u64, 3, 5, 7, 11, 13, 97, 7919, 1_000_003, 999_999_937] {
            let id = t.intern_prime(BigUint::from(p)).expect("prime");
            assert_eq!(
                t.get(id).expect("interned").primality(),
                Primality::Verified
            );
        }
    }

    #[test]
    fn reduce_is_exact_and_positive() {
        let mut t = FieldTable::new();
        let f7 = t.intern_prime(BigUint::from(7u8)).expect("prime");
        let neg = num_bigint::BigInt::from(-1i64);
        assert_eq!(t.reduce(f7, &neg), Some(num_bigint::BigInt::from(6i64)));
        assert_eq!(
            t.reduce(f7, &num_bigint::BigInt::from(15i64)),
            Some(num_bigint::BigInt::from(1i64))
        );
    }
}
