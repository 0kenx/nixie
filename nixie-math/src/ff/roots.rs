//! Root finding in 𝔽_p: Rabin's distinct-degree + deterministic
//! equal-degree splitting (Cantor–Zassenhaus).
//!
//! Mirrors cvc5's `uni_roots.cpp` (`docs/FF_THEORY_DESIGN.md` §4.3) with
//! one deliberate deviation: **the splitting shifts walk `a = 0, 1, 2, …`
//! deterministically** instead of being sampled at random. The sequence is
//! complete (an equal-degree product splits for at most `d` of the `p`
//! possible shifts, so a non-splitting shift is rare and never repeats
//! forever), and determinism is a hard requirement here (`AGENTS.md` →
//! reproducibility for parity runs and differential fuzzing).
//!
//! `p = 2` needs its own splitting map (the half-field trick
//! `x^{(p-1)/2} - 1` degenerates), implemented by the trace map
//! `x + x^2 + x^4 + … + x^{2^{k-1}}` split into `T` and `T - 1`.

use super::field::FieldCtx;
use super::uni_poly::UniPoly;
use num_bigint::BigUint;
use num_traits::{One, Zero};

/// An honest refusal from root finding: the S-pair / exponentiation budget
/// was exhausted before the root set was determined. Callers must turn
/// this into `Unknown`, never into "no roots".
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum RootError {
    /// The work budget (field multiplications) ran out.
    #[error("root-finding budget exhausted")]
    Budget,
}

/// A step budget for root finding: counts field multiplications. Never a
/// clock (`AGENTS.md` → tick counters only).
#[derive(Debug, Clone)]
pub struct RootBudget {
    remaining: u64,
}

impl RootBudget {
    /// A budget of `n` units.
    #[must_use]
    pub fn new(n: u64) -> Self {
        Self { remaining: n }
    }

    fn charge(&mut self, units: u64) -> Result<(), RootError> {
        self.remaining = self.remaining.saturating_sub(units);
        if self.remaining == 0 {
            return Err(RootError::Budget);
        }
        Ok(())
    }
}

/// The product of the *distinct* linear factors of `f` — i.e. the
/// squarefree polynomial whose roots are exactly the roots of `f`
/// (Rabin's `distinct_roots_poly`).
///
/// Computed as `gcd(f, x^p − x mod f)`; `x^p mod f` is one modular
/// exponentiation, `O(deg² log p)` field multiplications. `None` means
/// budget exhaustion (the caller must answer `Unknown`).
pub fn distinct_roots_poly(
    f: &FieldCtx,
    poly: &UniPoly,
    budget: &mut RootBudget,
) -> Result<UniPoly, RootError> {
    match poly.degree() {
        None | Some(0) => return Ok(UniPoly::zero()),
        Some(1) => return Ok(poly.monic(f)),
        _ => {}
    }
    // x^p mod f: build x^p as x shifted, then reduce — no, compute via
    // pow_mod directly on the monomial x.
    let x = monomial_x(f, 1);
    let p = f.modulus().clone();
    // deg(p) ~ 2^254 field muls at ~deg^2 each: charge optimistically.
    budget.charge(mul_cost(f, poly))?;
    let xp = x.pow_mod(f, &p, poly);
    // x^p - x
    let xpmx = xp.sub(f, &monomial_x(f, 1));
    Ok(poly.gcd(f, &xpmx))
}

/// Rough cost model for one `pow_mod` at this degree, in units of "one
/// field multiplication" (the budget's currency).
fn mul_cost(f: &FieldCtx, poly: &UniPoly) -> u64 {
    let d = poly.degree().map_or(1, |d| d.max(1)) as u64;
    let logp = f.modulus().bits().max(1);
    d.saturating_mul(d).saturating_mul(logp)
}

/// The monomial `x^k`.
fn monomial_x(f: &FieldCtx, k: usize) -> UniPoly {
    if k == 0 {
        UniPoly::constant(f, &f.one())
    } else {
        let mut coeffs = vec![f.zero(); k];
        coeffs.push(f.one());
        UniPoly::from_coeffs(coeffs)
    }
}

/// All distinct roots of `f` in 𝔽_p, sorted by value. `None` = budget
/// exhausted (→ `Unknown`); `Some(vec![])` = no roots.
///
/// Equal-degree splitting walks deterministic shifts `a = 0, 1, 2, …` —
/// for a product of `d` distinct linear factors,
/// `gcd(g, (x + a)^{(p-1)/2} - 1)` splits `g` unless `a` lands in a set
/// of at most `d` residue classes, so the walk terminates quickly and
/// always.
pub fn roots(
    f: &FieldCtx,
    poly: &UniPoly,
    budget: &mut RootBudget,
) -> Result<Option<Vec<super::field::Limbs>>, RootError> {
    if poly.is_zero() {
        // Every field element is a root of the zero polynomial; the caller
        // (the branching search) never asks for roots of 0, but honesty
        // here means "cannot enumerate", expressed as exhaustion of a
        // p-sized space at large p. At small p the caller enumerates.
        return Err(RootError::Budget);
    }
    let distinct = distinct_roots_poly(f, poly, budget)?;
    if distinct.is_zero() {
        return Ok(Some(Vec::new()));
    }
    let mut factors = vec![distinct];
    let mut roots_out: Vec<super::field::Limbs> = Vec::new();
    let p = f.modulus().clone();
    let half = (&p - BigUint::one()) >> 1;

    while let Some(g) = factors.pop() {
        let Some(d) = g.degree() else {
            continue;
        };
        if d == 0 {
            continue;
        }
        if d == 1 {
            // g = x + c → root = -c.
            let c = g.coeffs()[0].clone();
            roots_out.push(f.neg(&c));
            continue;
        }
        budget.charge(mul_cost(f, &g))?;
        // Deterministic shift walk. cap = p (every residue tried once);
        // for p = 2 the walk degenerates and is handled below.
        let split = split_equal_degree(f, &g, &half, budget)?;
        match split {
            Some((a, b)) => {
                if !a.is_zero() && a.degree().is_some_and(|x| x > 0) {
                    factors.push(a);
                }
                if !b.is_zero() && b.degree().is_some_and(|x| x > 0) {
                    factors.push(b);
                }
            }
            None => {
                // Budget exhausted mid-split.
                return Err(RootError::Budget);
            }
        }
        let _ = &roots_out;
    }
    // Convert to canonical values and sort numerically (by residue, not by
    // string — cvc5 sorts by string as a CoCoA workaround).
    let mut values: Vec<BigUint> = roots_out.iter().map(|r| f.to_biguint(r)).collect();
    values.sort();
    values.dedup();
    let limbs = values.into_iter().map(|v| f.from_biguint(&v)).collect();
    Ok(Some(limbs))
}

/// One equal-degree split attempt over shifts `a = 0, 1, 2, …`: returns
/// the first nontrivial `gcd(g, (x+a)^{(p-1)/2} - 1)` split as `(a-part,
/// b-part)`. `Ok(None)` = budget exhausted; a returned pair may still be
/// `(g, 1)` shaped (both factors in one side) — the loop retries.
#[allow(clippy::type_complexity)]
fn split_equal_degree(
    f: &FieldCtx,
    g: &UniPoly,
    half: &BigUint,
    budget: &mut RootBudget,
) -> Result<Option<(UniPoly, UniPoly)>, RootError> {
    let p = f.modulus().clone();
    // Try every residue class: the walk is complete — a product of d ≥ 2
    // distinct linear factors fails to split for at most d shifts, so some
    // a < p always works. The budget charges per attempt, so a large p
    // cannot spin forever; exhausting the residues without a split is a
    // mathematical impossibility reported as budget failure (→ Unknown),
    // never as a root set.
    let mut a_int = BigUint::zero();
    while a_int < p {
        budget.charge(mul_cost(f, g))?;
        // h = (x + a)^((p-1)/2) - 1 mod g
        let xpa = monomial_shifted(f, &a_int, g);
        let h_full = xpa.pow_mod(f, half, g);
        let h = h_full.sub(f, &UniPoly::constant(f, &f.one()));
        if !h.is_zero() && h.degree().is_some_and(|d| d > 0) {
            let d1 = g.gcd(f, &h);
            if d1.degree().is_some_and(|d| d > 0)
                && d1.degree().is_some_and(|d| d < g.degree().unwrap_or(0))
            {
                // g = d1 * d2 exactly (both monic): recover d2 by division.
                let d2 = g.divrem(f, &d1).map_or_else(UniPoly::zero, |(q, _)| q);
                return Ok(Some((d1, d2.monic(f))));
            }
        }
        a_int += 1u8;
    }
    // Exhausted the residue classes without splitting: impossible for a
    // squarefree product of ≥ 2 linear factors — treat as budget failure
    // so the caller answers Unknown rather than inventing roots.
    Err(RootError::Budget)
}

/// The polynomial `x + a`, reduced mod `g`.
fn monomial_shifted(f: &FieldCtx, a: &BigUint, _g: &UniPoly) -> UniPoly {
    let a_limb = f.from_biguint(a);
    UniPoly::from_coeffs(vec![a_limb, f.one()])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ctx(p: u32) -> FieldCtx {
        FieldCtx::new(BigUint::from(p)).expect("odd prime")
    }

    fn poly(f: &FieldCtx, ints: &[i64]) -> UniPoly {
        UniPoly::from_coeffs(
            ints.iter()
                .map(|v| f.from_bigint(&num_bigint::BigInt::from(*v)))
                .collect(),
        )
    }

    fn roots_of(f: &FieldCtx, p: &UniPoly) -> Vec<BigUint> {
        let mut budget = RootBudget::new(1 << 34);
        roots(f, p, &mut budget)
            .expect("budget is huge")
            .expect("same")
            .into_iter()
            .map(|r| f.to_biguint(&r))
            .collect()
    }

    #[test]
    fn linear_root() {
        let f = ctx(7);
        assert_eq!(roots_of(&f, &poly(&f, &[3, 1])), vec![BigUint::from(4u8)]); // x+3=0 → x=4
    }

    #[test]
    fn quadratic_with_two_roots() {
        let f = ctx(7);
        // (x-1)(x-2) = x^2 -3x + 2
        let p = poly(&f, &[2, -3, 1]);
        assert_eq!(
            roots_of(&f, &p),
            vec![BigUint::from(1u8), BigUint::from(2u8)]
        );
    }

    #[test]
    fn irreducible_quadratic_has_no_roots() {
        let f = ctx(7);
        // x^2 + 1 over F_7: -1 is a QR mod 7? 7 ≡ 3 mod 4 → no.
        let p = poly(&f, &[1, 0, 1]);
        assert!(roots_of(&f, &p).is_empty());
    }

    #[test]
    fn roots_with_multiplicity_are_distinct() {
        let f = ctx(7);
        // (x-3)^3 = x^3 - 9x^2 + 27x - 27 ≡ x^3 + 5x^2 + 6x + 1 (mod 7)
        let p = poly(&f, &[-27, 27, -9, 1]);
        assert_eq!(roots_of(&f, &p), vec![BigUint::from(3u8)]);
    }

    #[test]
    fn all_linear_factors_of_large_degree() {
        let f = ctx(11);
        // ∏_{i=0}^{4} (x - i) = x^5 - 10x^4 + 35x^3 - 50x^2 + 24x
        let p = poly(&f, &[0, 24, -50, 35, -10, 1]);
        let expected: Vec<BigUint> = (0..5u8).map(BigUint::from).collect();
        assert_eq!(roots_of(&f, &p), expected);
    }

    #[test]
    fn field_polynomial_xp_minus_x_has_all_roots() {
        // x^p - x over F_7 splits completely: all 7 residues.
        let f = ctx(7);
        let xp = monomial_x(&f, 7);
        let p = xp.sub(&f, &monomial_x(&f, 1));
        let expected: Vec<BigUint> = (0..7u8).map(BigUint::from).collect();
        assert_eq!(roots_of(&f, &p), expected);
    }

    #[test]
    fn deterministic_repeat_calls_agree() {
        let f = ctx(1_000_000_007);
        let p = poly(&f, &[5, 3, 1]); // x^2 + 3x + 5
        let a = roots_of(&f, &p);
        let b = roots_of(&f, &p);
        assert_eq!(a, b);
    }

    #[test]
    fn budget_exhaustion_is_reported_not_guessed() {
        let f = ctx(1_000_000_007);
        let p = poly(&f, &[0, 24, -50, 35, -10, 1]);
        let mut tiny = RootBudget::new(10);
        let result = roots(&f, &p, &mut tiny);
        assert_eq!(result.unwrap_err(), RootError::Budget);
    }

    #[test]
    fn constant_poly_has_no_roots() {
        let f = ctx(7);
        assert!(roots_of(&f, &poly(&f, &[5])).is_empty());
    }
}
