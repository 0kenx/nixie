//! Prime finite fields 𝔽_p for the `QF_FF` theory (`docs/FF_THEORY_DESIGN.md` §4.1).
//!
//! Elements are stored in Montgomery form (`a·R mod p`, `R = 2^{64·n}`) over
//! 64-bit limbs, `SmallVec<[u64; 4]>` so the ZK primes (BN254 / BLS12-381
//! scalar fields, Pallas/Vesta — 4 limbs; Goldilocks, BabyBear, Mersenne31 —
//! 1 limb) stay inline and allocation-free.
//!
//! ## Exactness
//!
//! There is no `u64` fast path that drops high limbs (`AGENTS.md` → *Wide
//! bit-vectors and bignums are exact*): the limb count is sized to `p` once,
//! in [`FieldCtx::new`], and every operation runs at that width. A 1-limb
//! field is handled by the *same* code with `n_limbs == 1`, not by a separate
//! truncated path.
//!
//! ## Determinism
//!
//! Constant-time is explicitly **not** a requirement — this is a solver, not
//! a crypto library. What *is* required is that nothing here reads a clock or
//! a random source: search-shaping decisions above this layer must be
//! reproducible.
//!
//! This module is deliberately self-contained (no dependency on the rational
//! Gröbner machinery): the ℚ engines carry normalization and coefficient-
//! growth mitigations tied to ℚ, and NRA is a live, sound path a generics
//! refactor would put at risk for no gain. Duplication is the cheaper trade.

use num_bigint::BigUint;
use num_traits::{One, Zero};
use smallvec::SmallVec;

/// A prime field's parameters, with the Montgomery constants derived once.
#[derive(Debug, Clone)]
pub struct FieldCtx {
    /// The modulus `p` (odd prime, `p ≥ 3`).
    p: BigUint,
    /// Limb count `n`: `2^{64(n-1)} ≤ p < 2^{64n}`.
    n_limbs: usize,
    /// `R = 2^{64n} mod p`.
    r: Limbs,
    /// `R² mod p`, for converting into Montgomery form.
    r2: Limbs,
    /// `p' = -p^{-1} mod 2^{64}`.
    n0: u64,
    /// `p` as limbs (little-endian), zero-padded to `n_limbs`.
    p_limbs: Limbs,
}

/// A field element in Montgomery form, relative to the [`FieldCtx`] it was
/// created through. Limbs are little-endian and always fully reduced
/// (`< p`), so equality of `Fp` values is limb-wise equality.
pub type Limbs = SmallVec<[u64; 4]>;

/// Errors from field construction / conversion.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum FieldCtxError {
    /// The modulus is even: Montgomery form needs `p` odd. `𝔽_2` is handled
    /// by the caller with an exact `BigUint` path (see `uni_poly` tests and
    /// `FieldCtx::is_two()` probes); it cannot use Montgomery arithmetic.
    #[error("Montgomery form requires an odd modulus; p = 2 needs the exact path")]
    EvenModulus,
    /// The modulus is smaller than 3 (`p = 2` is even; `p < 2` is no field).
    #[error("a prime field needs an odd prime p ≥ 3, got {0}")]
    TooSmall(String),
}

impl FieldCtx {
    /// Build the context for an odd prime `p ≥ 3`.
    ///
    /// The caller is responsible for primality (the AST layer's
    /// `FieldTable` classifies orders before any `FieldCtx` is built; here
    /// trusting a composite `p` would silently produce ring arithmetic mod
    /// a composite — every consumer constructs contexts only from
    /// classified prime orders).
    ///
    /// # Errors
    /// See [`FieldCtxError`].
    pub fn new(p: BigUint) -> Result<Self, FieldCtxError> {
        if (&p % 2u32).is_zero() {
            if p == BigUint::from(2u8) {
                return Err(FieldCtxError::EvenModulus);
            }
            return Err(FieldCtxError::TooSmall(p.to_string()));
        }
        if p < BigUint::from(3u8) {
            return Err(FieldCtxError::TooSmall(p.to_string()));
        }
        let n_limbs = p.bits().div_ceil(64).max(1) as usize;
        let shift = 64 * n_limbs;
        // R = 2^shift mod p, computed exactly in BigUint (no modular
        // exponentiation shortcut can be trusted before n0 exists).
        let _ = BigUint::one();
        let r_int = (BigUint::from(1u8) << shift) % &p;
        let r2_int = (&r_int * &r_int) % &p;
        // R and R² in Montgomery form must themselves be Montgomery limbs,
        // not raw integers: r = R mod p converts through `from_biguint`
        // after the raw values exist.
        let p_limbs = pad_limbs(&to_limbs(&p), n_limbs);
        let n0 = inv64_wrapped(p_limbs[0]);
        let ctx = Self {
            p,
            n_limbs,
            r: Limbs::new(),
            r2: Limbs::new(),
            n0,
            p_limbs,
        };
        // Convert R and R² through the raw-int path: mul_raw(a, 1) reduces
        // a out of Montgomery form, so to build the Montgomery encodings we
        // use R²·v as usual — but R itself must be built by the identity
        // below. Standard construction: with limbs of v = raw(v),
        // mont(v) = mul_raw(v_limbs, R²). Build R² first via a BigUint
        // modular multiply in raw limbs: R² mod p is already exact as an
        // integer; converting it needs mul_raw(raw(R²), R²)… circular.
        //
        // Break the circle the usual way: CIOS with a = raw value and
        // b = raw 1 computes REDC(a·1) = a·R^{-1}… not what we want either.
        // The primitive that *is* available: mul_raw on raw limbs performs
        // REDC(xy) = x·y·R^{-1}. So mont(v) = REDC(v·R²) = mul_raw(v, R²)
        // needs R² in raw limbs — which we have exactly (r2_int). And
        // mont(1) = mul_raw(1, R²) = R. So: store r2 as RAW limbs of R² mod
        // p and use it only through from_biguint; store r as mont(1).
        let r2_raw = pad_limbs(&to_limbs(&r2_int), n_limbs);
        let one_raw = {
            let mut l = Limbs::with_capacity(n_limbs);
            l.resize(n_limbs, 0);
            l[0] = 1;
            l
        };
        // `mul_raw` reads only n_limbs/n0/p_limbs, so it is available on the
        // partially-initialized context.
        let mut ctx = ctx;
        ctx.r = ctx.mul_raw(&one_raw, &r2_raw); // mont(1) = REDC(1 · R²) = R
        ctx.r2 = r2_raw;
        Ok(ctx)
    }

    /// The modulus.
    #[must_use]
    pub fn modulus(&self) -> &BigUint {
        &self.p
    }

    /// The limb width every element of this field uses.
    #[must_use]
    pub fn n_limbs(&self) -> usize {
        self.n_limbs
    }

    /// The additive identity, in Montgomery form.
    #[must_use]
    pub fn zero(&self) -> Limbs {
        smallvec::smallvec![0u64; self.n_limbs]
    }

    /// The multiplicative identity, in Montgomery form.
    #[must_use]
    pub fn one(&self) -> Limbs {
        self.r.clone()
    }

    /// Convert an exact integer into Montgomery form.
    #[must_use]
    pub fn from_biguint(&self, v: &BigUint) -> Limbs {
        let reduced = v % &self.p;
        let limbs = pad_limbs(&to_limbs(&reduced), self.n_limbs);
        self.mul_raw(&limbs, &self.r2)
    }

    /// Convert an exact (possibly negative) integer into Montgomery form.
    #[must_use]
    pub fn from_bigint(&self, v: &num_bigint::BigInt) -> Limbs {
        match v.sign() {
            num_bigint::Sign::Minus => {
                let mag = v.magnitude();
                let reduced = &self.p - (mag % &self.p);
                self.from_biguint(&reduced)
            }
            _ => self.from_biguint(v.magnitude()),
        }
    }

    /// Convert out of Montgomery form into an exact integer in `[0, p)`.
    #[must_use]
    pub fn to_biguint(&self, v: &Limbs) -> BigUint {
        let reduced = self.reduce_once(v);
        from_limbs(&reduced)
    }

    /// Whether `v` (in Montgomery form) is zero.
    #[must_use]
    pub fn is_zero(&self, v: &Limbs) -> bool {
        v.iter().all(|&l| l == 0)
    }

    /// Field addition. Inputs must be canonical (< p); the result is
    /// canonical.
    #[must_use]
    pub fn add(&self, a: &Limbs, b: &Limbs) -> Limbs {
        let mut sum = Limbs::with_capacity(self.n_limbs);
        let mut carry = 0u128;
        for i in 0..self.n_limbs {
            let s = u128::from(a[i]) + u128::from(b[i]) + carry;
            sum.push(s as u64);
            carry = s >> 64;
        }
        // One conditional subtract: a, b < p ≤ 2^{64n}-1, so sum < 2p fits
        // the extra bit; subtracting p when ≥ p canonicalizes.
        if carry != 0 || self.cmp_ge_p(&sum) {
            sub_assign_p(&mut sum, &self.p_limbs);
        }
        sum
    }

    /// Field negation.
    #[must_use]
    pub fn neg(&self, a: &Limbs) -> Limbs {
        if self.is_zero(a) {
            return self.zero();
        }
        // p - a (a < p, a ≠ 0, so no borrow), already in Montgomery form
        // because Montgomery form is a bijection on [0, p).
        let mut out = Limbs::with_capacity(self.n_limbs);
        let mut borrow = 0u128;
        for i in 0..self.n_limbs {
            let d = u128::from(self.p_limbs[i]) + borrow;
            let ai = u128::from(a[i]);
            if d >= ai {
                out.push((d - ai) as u64);
                borrow = 0;
            } else {
                out.push((d + (1u128 << 64) - ai) as u64);
                borrow = 1;
            }
        }
        out
    }

    /// Field subtraction `a - b`.
    #[must_use]
    pub fn sub(&self, a: &Limbs, b: &Limbs) -> Limbs {
        self.add(a, &self.neg(b))
    }

    /// Montgomery multiplication. Inputs are Montgomery-form (any canonical
    /// values); the result is Montgomery form. This is the core primitive —
    /// CIOS with per-limb reduction, exact at every step.
    #[must_use]
    pub fn mul_raw(&self, a: &Limbs, b: &Limbs) -> Limbs {
        let n = self.n_limbs;
        // t has n+2 limbs: the accumulator. Using u128 limbs would overflow
        // on the final adds, so u64 limbs with u128 column arithmetic.
        let mut t = vec![0u64; n + 2];
        for i in 0..n {
            // t += a[i] * b
            let mut carry = 0u128;
            for j in 0..n {
                let cur = u128::from(t[j]) + u128::from(a[i]) * u128::from(b[j]) + carry;
                t[j] = cur as u64;
                carry = cur >> 64;
            }
            let cur = u128::from(t[n]) + carry;
            t[n] = cur as u64;
            t[n + 1] = (t[n + 1] as u128 + (cur >> 64)) as u64;
            // m = t[0] * n0 mod 2^64
            let m = t[0].wrapping_mul(self.n0);
            // t += m * p; t >>= 64 (the low limb becomes exactly 0)
            let cur = u128::from(t[0]) + u128::from(m) * u128::from(self.p_limbs[0]);
            let mut carry = cur >> 64;
            for j in 1..n {
                let cur = u128::from(t[j]) + u128::from(m) * u128::from(self.p_limbs[j]) + carry;
                t[j - 1] = cur as u64;
                carry = cur >> 64;
            }
            let cur = u128::from(t[n]) + carry;
            t[n - 1] = cur as u64;
            t[n] = t[n + 1] + ((cur >> 64) as u64);
            t[n + 1] = 0;
        }
        // Result is t[0..n] (plus the overflow bit t[n]); it is < 2p.
        let mut out = Limbs::from_iter(t[..n].iter().copied());
        if t[n] != 0 || self.cmp_ge_p(&out) {
            sub_assign_p(&mut out, &self.p_limbs);
        }
        out
    }

    /// Field multiplication (both operands Montgomery form).
    #[must_use]
    pub fn mul(&self, a: &Limbs, b: &Limbs) -> Limbs {
        self.mul_raw(a, b)
    }

    /// Field squaring.
    #[must_use]
    pub fn square(&self, a: &Limbs) -> Limbs {
        self.mul_raw(a, a)
    }

    /// Exponentiation by an exact integer exponent (square-and-multiply,
    /// Montgomery ladder-free: no side-channel requirement, see module doc).
    #[must_use]
    pub fn pow(&self, a: &Limbs, e: &BigUint) -> Limbs {
        let mut result = self.one();
        if e.is_zero() {
            return result;
        }
        let mut base = a.clone();
        let bits = e.bits();
        for i in 0..bits {
            if e.bit(i) {
                result = self.mul_raw(&result, &base);
            }
            base = self.mul_raw(&base, &base);
        }
        result
    }

    /// Multiplicative inverse; `None` exactly when `a` is zero (a field has
    /// no zero divisor, so this is the complete failure condition).
    #[must_use]
    pub fn inv(&self, a: &Limbs) -> Option<Limbs> {
        if self.is_zero(a) {
            return None;
        }
        // a^{p-2} by Fermat. Slower than binary extended Euclid for 1 limb,
        // but branch-sparse and exact; the hot loops use batch_inv anyway.
        let e = &self.p - BigUint::from(2u8);
        Some(self.pow(a, &e))
    }

    /// Batch inversion (Montgomery's trick): one inversion per *segment*
    /// plus `O(k)` multiplications for `k` values. A zero value separates
    /// segments (it has no inverse) and inverts to `None` individually
    /// without poisoning its neighbours.
    #[must_use]
    pub fn batch_inv(&self, values: &[Limbs]) -> Vec<Option<Limbs>> {
        let mut out: Vec<Option<Limbs>> = vec![None; values.len()];
        let mut seg_start = 0usize;
        while seg_start < values.len() {
            // Find the segment: [seg_start, seg_end) with no zeros.
            let mut seg_end = seg_start;
            while seg_end < values.len() && !self.is_zero(&values[seg_end]) {
                seg_end += 1;
            }
            if seg_end > seg_start {
                self.batch_inv_segment(&values[seg_start..seg_end], &mut out[seg_start..seg_end]);
            }
            // Skip the zero (if any); its output stays `None`.
            seg_start = seg_end + 1;
        }
        out
    }

    /// The standard trick on one all-nonzero segment: prefix products, one
    /// inversion, a backward walk.
    fn batch_inv_segment(&self, seg: &[Limbs], out: &mut [Option<Limbs>]) {
        debug_assert_eq!(seg.len(), out.len());
        let mut prefix: Vec<Limbs> = Vec::with_capacity(seg.len());
        let mut acc = self.one();
        for v in seg {
            acc = self.mul_raw(&acc, v);
            prefix.push(acc.clone());
        }
        // inv_prefix[i] = (v_start ..= v_i)^{-1}, built backward with one
        // inversion total.
        let mut inv_prefix: Vec<Limbs> = vec![self.zero(); seg.len()];
        let last = self
            .inv(prefix.last().unwrap_or(&self.zero()))
            .unwrap_or_else(|| self.one());
        inv_prefix[seg.len() - 1] = last;
        for i in (1..seg.len()).rev() {
            inv_prefix[i - 1] = self.mul_raw(&inv_prefix[i], &seg[i]);
        }
        // v_i^{-1} = inv_prefix[i] * prefix[i-1]  (prefix[-1] := 1)
        out[0] = Some(inv_prefix[0].clone());
        for i in 1..seg.len() {
            out[i] = Some(self.mul_raw(&inv_prefix[i], &prefix[i - 1]));
        }
    }

    /// Equality of two Montgomery-form values.
    #[must_use]
    pub fn eq(&self, a: &Limbs, b: &Limbs) -> bool {
        a == b
    }

    /// Whether `v ≥ p` (limb-wise, same width).
    fn cmp_ge_p(&self, v: &[u64]) -> bool {
        for i in (0..self.n_limbs).rev() {
            if v[i] > self.p_limbs[i] {
                return true;
            }
            if v[i] < self.p_limbs[i] {
                return false;
            }
        }
        true // equal
    }

    /// Montgomery reduction of a canonical Montgomery-form value back to the
    /// integer residue: multiply by 1 (i.e. reduce the Montgomery
    /// representation).
    #[must_use]
    fn reduce_once(&self, v: &Limbs) -> Limbs {
        self.mul_raw(v, &self.one_raw())
    }

    /// The raw limb encoding of 1 (NOT Montgomery form).
    fn one_raw(&self) -> Limbs {
        let mut l = self.zero();
        l[0] = 1;
        l
    }
}

/// `v -= p` (in place, assumes `v ≥ p`; widths equal).
fn sub_assign_p(v: &mut Limbs, p: &Limbs) {
    let mut borrow = 0i128;
    for i in 0..v.len() {
        let d = i128::from(v[i]) - i128::from(p[i]) - borrow;
        if d < 0 {
            v[i] = (d + (1i128 << 64)) as u64;
            borrow = 1;
        } else {
            v[i] = d as u64;
            borrow = 0;
        }
    }
}

/// `-n^{-1} mod 2^{64}` (Newton iteration; exact for odd `n0`).
fn inv64_wrapped(a: u64) -> u64 {
    debug_assert!(!a.is_multiple_of(2));
    // inv = a^{2^63 - 1} mod 2^64 by Fermat for the group of odd residues.
    let mut inv = 1u64;
    for _ in 0..63 {
        inv = inv.wrapping_mul(inv);
        inv = inv.wrapping_mul(a);
    }
    inv.wrapping_neg()
}

/// Little-endian 64-bit limbs of a `BigUint` (num-bigint exposes radix-256
/// bytes; packed eight per limb).
fn to_limbs(v: &BigUint) -> Limbs {
    let bytes = v.to_radix_le(256);
    let mut out = Limbs::with_capacity(bytes.len().div_ceil(8));
    for (i, b) in bytes.iter().enumerate() {
        let limb = i / 8;
        if limb == out.len() {
            out.push(0);
        }
        out[limb] |= u64::from(*b) << (8 * (i % 8));
    }
    out
}

/// BigUint from little-endian 64-bit limbs.
fn from_limbs(v: &Limbs) -> BigUint {
    let mut bytes = Vec::with_capacity(v.len() * 8);
    for limb in v {
        for b in limb.to_le_bytes() {
            bytes.push(b);
        }
    }
    BigUint::from_radix_le(&bytes, 256).unwrap_or_else(BigUint::zero)
}

/// Zero-pad/truncate a limb vector to exactly `n` limbs.
fn pad_limbs(v: &Limbs, n: usize) -> Limbs {
    let mut out = v.clone();
    out.resize(n, 0);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ctx(p: u64) -> FieldCtx {
        FieldCtx::new(BigUint::from(p)).expect("odd prime")
    }

    #[test]
    fn round_trip_small_primes() {
        for p in [3u64, 5, 7, 11, 13, 97, 7919, 1_000_000_007] {
            let f = ctx(p);
            for x in 0..p.min(50) {
                let mont = f.from_biguint(&BigUint::from(x));
                assert_eq!(f.to_biguint(&mont), BigUint::from(x), "p={p} x={x}");
            }
        }
    }

    #[test]
    fn field_axioms_hold() {
        // Commutativity, identity, inverse, distributivity on F_97.
        let f = ctx(97);
        let v: Vec<Limbs> = (0..20u64)
            .map(|x| f.from_biguint(&BigUint::from(x)))
            .collect();
        for a in &v {
            assert!(f.is_zero(&f.sub(a, a)));
            assert_eq!(f.add(a, &f.zero()), *a);
            assert_eq!(f.mul(a, &f.one()), *a);
            if !f.is_zero(a) {
                let inv = f.inv(a).expect("nonzero invertible");
                assert_eq!(f.mul(a, &inv), f.one());
            }
            for b in &v {
                assert_eq!(f.add(a, b), f.add(b, a));
                assert_eq!(f.mul(a, b), f.mul(b, a));
                for c in &v {
                    // distributivity
                    assert_eq!(f.mul(a, &f.add(b, c)), f.add(&f.mul(a, b), &f.mul(a, c)));
                }
            }
        }
    }

    #[test]
    fn one_limb_and_four_limb_agree_with_bigint() {
        // Goldilocks p = 2^64 - 2^32 + 1 (1 limb) and BN254 scalar (4 limbs):
        // exactness pinned against BigUint arithmetic.
        let goldilocks: BigUint =
            (BigUint::from(1u8) << 64) - (BigUint::from(1u8) << 32) + BigUint::from(1u8);
        let f = FieldCtx::new(goldilocks.clone()).expect("goldilocks is an odd prime");
        assert_eq!(f.n_limbs(), 1);
        let a = f.from_biguint(&(goldilocks.clone() - 5u8));
        let b = f.from_biguint(&BigUint::from(123456789u64));
        let prod = f.mul(&a, &b);
        let expected = ((goldilocks.clone() - 5u8) * 123456789u64) % &goldilocks;
        assert_eq!(f.to_biguint(&prod), expected);

        let bn254: BigUint =
            "21888242871839275222246405745257275088548364400416034343698204186575808495617"
                .parse()
                .expect("parses");
        let f = FieldCtx::new(bn254.clone()).expect("BN254 scalar is an odd prime");
        assert_eq!(f.n_limbs(), 4);
        let a = f.from_biguint(&(bn254.clone() - 1u8));
        let b = f.from_biguint(&BigUint::from(7u8));
        // (p-1)*7 = -7 = p-7 mod p
        assert_eq!(f.to_biguint(&f.mul(&a, &b)), bn254.clone() - 7u8);
        // (p-1)^2 = 1 mod p
        assert_eq!(f.to_biguint(&f.square(&a)), BigUint::from(1u8));
    }

    #[test]
    fn pow_matches_repeated_squaring() {
        let f = ctx(1_000_000_007);
        let a = f.from_biguint(&BigUint::from(3u8));
        let mut acc = f.one();
        for e in 0..40u64 {
            assert_eq!(f.pow(&a, &BigUint::from(e)), acc);
            acc = f.mul(&acc, &a);
        }
    }

    #[test]
    fn negative_conversion() {
        let f = ctx(97);
        let neg_one = f.from_bigint(&num_bigint::BigInt::from(-1));
        assert_eq!(f.to_biguint(&neg_one), BigUint::from(96u8));
        let neg_big = f.from_bigint(&num_bigint::BigInt::from(-1000));
        // -1000 mod 97: 1000 = 10*97 + 30, so -1000 = -30 = 67
        assert_eq!(f.to_biguint(&neg_big), BigUint::from(67u8));
    }

    #[test]
    fn batch_inversion_agrees_with_individual() {
        let f = ctx(7919);
        let values: Vec<Limbs> = (1..=30u64)
            .map(|x| f.from_biguint(&BigUint::from(x)))
            .chain(std::iter::once(f.zero()))
            .collect();
        let batched = f.batch_inv(&values);
        for (v, inv) in values.iter().zip(&batched) {
            match inv {
                Some(i) => assert_eq!(f.mul(v, i), f.one()),
                None => assert!(f.is_zero(v)),
            }
        }
    }

    #[test]
    fn batch_inversion_with_leading_and_interior_zeros() {
        let f = ctx(13);
        let values: Vec<Limbs> = vec![
            f.zero(),
            f.from_biguint(&BigUint::from(2u8)),
            f.zero(),
            f.from_biguint(&BigUint::from(5u8)),
        ];
        let batched = f.batch_inv(&values);
        assert!(batched[0].is_none());
        assert!(batched[1].is_some());
        assert!(batched[2].is_none());
        assert!(batched[3].is_some());
    }

    #[test]
    fn even_modulus_is_rejected() {
        assert!(FieldCtx::new(BigUint::from(2u8)).is_err());
        assert!(FieldCtx::new(BigUint::from(4u8)).is_err());
        assert!(FieldCtx::new(BigUint::from(1u8)).is_err());
        assert!(FieldCtx::new(BigUint::zero()).is_err());
    }

    #[test]
    fn sub_neg_and_add_cancel_exactly() {
        let f = ctx(1_000_000_007);
        let a = f.from_biguint(&BigUint::from(999_999_999u64));
        let b = f.from_biguint(&BigUint::from(123u64));
        assert_eq!(f.add(&f.sub(&a, &b), &b), a.clone());
        assert_eq!(f.neg(&f.neg(&a)), a.clone());
    }
}
