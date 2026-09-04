//! Simplification of polynomials and constraints.
//!
//! This module provides simplification and normalization routines for
//! polynomial constraints to improve solver efficiency.
//!
//! Reference: Z3's `nlsat/nlsat_simplify.cpp`

use crate::types::{Atom, AtomKind, IneqAtom, PolyFactor};
use nixie_math::polynomial::Polynomial;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

/// Simplify a polynomial by removing common factors and normalizing.
pub fn simplify_polynomial(poly: &Polynomial) -> Polynomial {
    simplify_polynomial_with_sign(poly).0
}

/// Simplify a polynomial and report whether the canonicalization step
/// negated it (i.e. the original leading coefficient was negative).
///
/// Callers that compare the simplified polynomial against zero (as
/// [`simplify_ineq_atom`] does) MUST account for the returned flip flag,
/// since negating `p` inverts the sign of `p` at every point and therefore
/// flips `p < 0` into `p > 0` (and vice versa) for the *original* polynomial.
fn simplify_polynomial_with_sign(poly: &Polynomial) -> (Polynomial, bool) {
    let result = poly.clone();

    // Remove zero polynomial
    if result.is_zero() {
        return (result, false);
    }

    // Factor out GCD of coefficients (for rational polynomials, this normalizes)
    normalize_coefficients(result)
}

/// Normalize polynomial coefficients by making the leading coefficient
/// positive. Returns the normalized polynomial along with whether a sign
/// flip (negation) was applied.
fn normalize_coefficients(poly: Polynomial) -> (Polynomial, bool) {
    let terms = poly.terms();

    if terms.is_empty() {
        return (poly, false);
    }

    // Find the GCD of all denominators and LCM would be complex,
    // so we just normalize the leading coefficient to be positive
    let leading_term = &terms[0];

    if leading_term.coeff.is_negative() {
        // Negate all coefficients
        (poly.neg(), true)
    } else {
        (poly, false)
    }
}

/// Simplify an inequality atom.
///
/// Each factor may be canonicalized to a positive leading coefficient by
/// `simplify_polynomial_with_sign`, which negates the polynomial (and thus
/// flips its sign at every point). For factors with odd multiplicity
/// (`is_even == false`) such a flip inverts the sign of the overall product,
/// so we track the cumulative parity of these flips (`flip_parity`) and use
/// it to invert `Lt`/`Gt` (and dropped-constant sign checks) so the
/// simplified atom remains equivalent to the original.
pub fn simplify_ineq_atom(atom: &IneqAtom) -> Option<SimplifiedAtom> {
    // Handle trivial cases
    if atom.factors.is_empty() {
        return Some(SimplifiedAtom::Trivial(false));
    }

    // Simplify each factor
    let mut simplified_factors = Vec::new();
    let mut has_zero = false;
    let mut flip_parity = false;

    for factor in &atom.factors {
        let (simplified, flipped) = simplify_polynomial_with_sign(&factor.poly);

        if simplified.is_zero() {
            has_zero = true;
            break;
        }

        // Only odd-multiplicity factors contribute their sign to the
        // product; even-multiplicity factors are always non-negative, so a
        // sign flip on them doesn't change the product's sign.
        if !factor.is_even && flipped {
            flip_parity = !flip_parity;
        }

        // Check if constant
        if simplified.is_constant() {
            let const_val = simplified.constant_term();

            // If this is the only factor, we can evaluate the constraint
            // directly. `const_val` is the sign-normalized magnitude; recover
            // the original (signed) value via `flip_parity`.
            if atom.factors.len() == 1 {
                let effective_val = if flip_parity {
                    -const_val.clone()
                } else {
                    const_val.clone()
                };
                return match atom.kind {
                    AtomKind::Eq => Some(SimplifiedAtom::Trivial(effective_val.is_zero())),
                    AtomKind::Lt => Some(SimplifiedAtom::Trivial(effective_val.is_negative())),
                    AtomKind::Gt => Some(SimplifiedAtom::Trivial(effective_val.is_positive())),
                    _ => None,
                };
            }

            // Handle constant factors based on atom kind
            match atom.kind {
                AtomKind::Eq => {
                    // p * c = 0 is equivalent to p = 0 if c != 0
                    if const_val.is_zero() {
                        return Some(SimplifiedAtom::Trivial(true));
                    }
                    // Otherwise skip this factor (its sign was already
                    // folded into flip_parity above).
                    continue;
                }
                AtomKind::Lt | AtomKind::Gt => {
                    // p * c < 0 or p * c > 0
                    if const_val.is_zero() {
                        return Some(SimplifiedAtom::Trivial(false));
                    }
                    // The constant's sign has already been folded into
                    // flip_parity above; drop it from the factor list.
                    continue;
                }
                _ => {}
            }
        }

        simplified_factors.push(PolyFactor {
            poly: simplified,
            is_even: factor.is_even,
        });
    }

    // Handle the zero case
    if has_zero {
        return match atom.kind {
            AtomKind::Eq => Some(SimplifiedAtom::Trivial(true)), // 0 = 0 is true
            AtomKind::Lt => Some(SimplifiedAtom::Trivial(false)), // 0 < 0 is false
            AtomKind::Gt => Some(SimplifiedAtom::Trivial(false)), // 0 > 0 is false
            _ => None,
        };
    }

    // If no factors remain, all factors were constants that were folded into
    // flip_parity; evaluate the (implicit, positive-magnitude) constraint
    // against the tracked sign.
    if simplified_factors.is_empty() {
        return match atom.kind {
            AtomKind::Eq => Some(SimplifiedAtom::Trivial(false)), // constant != 0
            AtomKind::Lt => Some(SimplifiedAtom::Trivial(flip_parity)),
            AtomKind::Gt => Some(SimplifiedAtom::Trivial(!flip_parity)),
            _ => None,
        };
    }

    // An odd number of sign flips across odd-multiplicity factors inverts
    // the comparison direction against zero (Eq is unaffected).
    let effective_kind = if flip_parity {
        match atom.kind {
            AtomKind::Lt => AtomKind::Gt,
            AtomKind::Gt => AtomKind::Lt,
            other => other,
        }
    } else {
        atom.kind
    };

    // Create simplified atom
    Some(SimplifiedAtom::Atom(Atom::Ineq(IneqAtom {
        kind: effective_kind,
        factors: simplified_factors,
        max_var: atom.max_var,
        bool_var: atom.bool_var,
    })))
}

/// Result of simplification.
#[derive(Debug, Clone)]
pub enum SimplifiedAtom {
    /// Atom simplified to a constant.
    Trivial(bool),
    /// Simplified atom.
    Atom(Atom),
}

/// Eliminate redundant constraints from a set of atoms.
pub fn eliminate_redundant(atoms: &[Atom]) -> Vec<usize> {
    let mut redundant = Vec::new();

    // Simple redundancy check: find duplicate atoms
    for i in 0..atoms.len() {
        for j in (i + 1)..atoms.len() {
            if atoms_equivalent(&atoms[i], &atoms[j]) {
                redundant.push(j);
            }
        }
    }

    // Deduplicate the redundant list
    redundant.sort_unstable();
    redundant.dedup();

    redundant
}

/// Check if two atoms are equivalent (represent the same constraint).
///
/// For `Eq` atoms, `p = 0` and `c * p = 0` denote the same constraint for
/// any non-zero scalar `c`, so any non-zero ratio is acceptable.
///
/// For `Lt`/`Gt` atoms this is *not* true: negating an odd-multiplicity
/// factor flips the sign of the product at every point, so `p < 0` and
/// `-p < 0` (i.e. `p > 0`) are complementary, not equivalent. We therefore
/// track the cumulative sign flip across odd-multiplicity factors (mirroring
/// [`simplify_ineq_atom`]'s `flip_parity`) and only report the atoms as
/// equivalent when that parity is even (no net sign flip). Even-multiplicity
/// factors never contribute a sign to the product, so a negative ratio on
/// those is harmless.
fn atoms_equivalent(a1: &Atom, a2: &Atom) -> bool {
    match (a1, a2) {
        (Atom::Ineq(ineq1), Atom::Ineq(ineq2)) => {
            if ineq1.kind != ineq2.kind {
                return false;
            }

            if ineq1.factors.len() != ineq2.factors.len() {
                return false;
            }

            // Check if all factors match (order-independent for multiplication)
            // For simplicity, we just check if they're identical in order
            let mut flip_parity = false;
            for (f1, f2) in ineq1.factors.iter().zip(ineq2.factors.iter()) {
                let Some(negated) = polynomials_equivalent(&f1.poly, &f2.poly) else {
                    return false;
                };
                if f1.is_even != f2.is_even {
                    return false;
                }
                if !f1.is_even && negated {
                    flip_parity = !flip_parity;
                }
            }

            match ineq1.kind {
                // p = 0 iff c*p = 0 for any non-zero c, regardless of sign.
                AtomKind::Eq => true,
                // p < 0 / p > 0 flip meaning under a net-negative scalar, so
                // only an even (net-positive) parity keeps the same atom.
                AtomKind::Lt | AtomKind::Gt => !flip_parity,
                _ => false,
            }
        }
        _ => false,
    }
}

/// Check if two polynomials are equivalent up to a non-zero constant factor.
///
/// Returns `Some(is_negative)` when `p1 == ratio * p2` for some non-zero
/// rational `ratio`, where `is_negative` records whether that ratio is
/// negative (i.e. whether the two polynomials have opposite sign at every
/// point). Returns `None` when no such ratio exists.
fn polynomials_equivalent(p1: &Polynomial, p2: &Polynomial) -> Option<bool> {
    use num_traits::Zero;

    let t1 = p1.terms();
    let t2 = p2.terms();

    // Both empty (zero polynomials) are equivalent (ratio is arbitrary,
    // treat as non-negative).
    if t1.is_empty() && t2.is_empty() {
        return Some(false);
    }

    // Different number of terms means different structure
    if t1.len() != t2.len() {
        return None;
    }

    // Find the ratio from the first pair of terms
    let mut ratio: Option<BigRational> = None;

    for (term1, term2) in t1.iter().zip(t2.iter()) {
        // Monomials must match exactly
        if term1.monomial != term2.monomial {
            return None;
        }

        // Check coefficient ratio
        if term2.coeff.is_zero() {
            // If term2's coeff is zero, term1's must also be zero
            if !term1.coeff.is_zero() {
                return None;
            }
            // Both zero, continue to next term
            continue;
        }

        // Compute the ratio term1.coeff / term2.coeff
        let current_ratio = &term1.coeff / &term2.coeff;

        match ratio {
            None => {
                // First non-zero ratio found
                ratio = Some(current_ratio);
            }
            Some(ref expected_ratio) => {
                // Check if this ratio matches the expected one
                if &current_ratio != expected_ratio {
                    return None;
                }
            }
        }
    }

    Some(ratio.map(|r| r.is_negative()).unwrap_or(false))
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_rational::BigRational;

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(n.into())
    }

    #[test]
    fn test_simplify_polynomial_zero() {
        let zero = Polynomial::zero();
        let simplified = simplify_polynomial(&zero);
        assert!(simplified.is_zero());
    }

    #[test]
    fn test_simplify_polynomial_constant() {
        let c = Polynomial::constant(rat(5));
        let simplified = simplify_polynomial(&c);
        assert_eq!(simplified.constant_term(), rat(5));
    }

    #[test]
    fn test_simplify_polynomial_negative() {
        let x = Polynomial::from_var(0);
        let neg_x = x.neg();
        let simplified = simplify_polynomial(&neg_x);

        // Leading coefficient should be positive after normalization
        let terms = simplified.terms();
        assert!(!terms.is_empty());
        assert!(terms[0].coeff.is_positive());
    }

    fn ineq_atom(kind: AtomKind, poly: Polynomial, is_even: bool) -> Atom {
        Atom::Ineq(IneqAtom {
            kind,
            factors: vec![PolyFactor { poly, is_even }],
            max_var: 0,
            bool_var: 0,
        })
    }

    // Regression test: `p < 0` and `-p < 0` (i.e. `p > 0`) are NOT the same
    // constraint, so `eliminate_redundant` must not delete one of them as a
    // duplicate of the other, even though they agree up to a constant factor.
    #[test]
    fn test_eliminate_redundant_does_not_conflate_negated_inequality() {
        let x = Polynomial::from_var(0);
        let neg_x = x.neg();

        let p_lt_0 = ineq_atom(AtomKind::Lt, x.clone(), false);
        let neg_p_lt_0 = ineq_atom(AtomKind::Lt, neg_x.clone(), false);

        let atoms = vec![p_lt_0, neg_p_lt_0];
        let redundant = eliminate_redundant(&atoms);
        assert!(
            redundant.is_empty(),
            "`x < 0` and `-x < 0` are complementary, not redundant: {redundant:?}"
        );
    }

    // `2*x < 0` is redundant with `x < 0` since scaling by a positive
    // constant preserves the sign.
    #[test]
    fn test_eliminate_redundant_detects_positive_scalar_duplicate() {
        let x = Polynomial::from_var(0);
        let two_x = x.scale(&BigRational::from_integer(2.into()));

        let p_lt_0 = ineq_atom(AtomKind::Lt, x, false);
        let scaled_lt_0 = ineq_atom(AtomKind::Lt, two_x, false);

        let atoms = vec![p_lt_0, scaled_lt_0];
        let redundant = eliminate_redundant(&atoms);
        assert_eq!(redundant, vec![1]);
    }

    // For equality atoms, `p = 0` and `-p = 0` describe the same zero set,
    // so they remain legitimately redundant.
    #[test]
    fn test_eliminate_redundant_still_merges_negated_equality() {
        let x = Polynomial::from_var(0);
        let neg_x = x.neg();

        let p_eq_0 = ineq_atom(AtomKind::Eq, x, false);
        let neg_p_eq_0 = ineq_atom(AtomKind::Eq, neg_x, false);

        let atoms = vec![p_eq_0, neg_p_eq_0];
        let redundant = eliminate_redundant(&atoms);
        assert_eq!(redundant, vec![1]);
    }

    #[test]
    fn test_simplify_ineq_zero() {
        let zero = Polynomial::zero();
        let atom = IneqAtom::from_poly(zero, AtomKind::Eq);

        let result = simplify_ineq_atom(&atom);
        assert!(matches!(result, Some(SimplifiedAtom::Trivial(true))));
    }

    #[test]
    fn test_simplify_ineq_constant_eq() {
        let c = Polynomial::constant(rat(5));
        let atom = IneqAtom::from_poly(c, AtomKind::Eq);

        let result = simplify_ineq_atom(&atom);
        // 5 = 0 is false
        assert!(matches!(result, Some(SimplifiedAtom::Trivial(false))));
    }

    #[test]
    fn test_simplify_ineq_constant_gt() {
        let c = Polynomial::constant(rat(5));
        let atom = IneqAtom::from_poly(c, AtomKind::Gt);

        let result = simplify_ineq_atom(&atom);
        // 5 > 0 is true
        assert!(matches!(result, Some(SimplifiedAtom::Trivial(true))));
    }

    #[test]
    fn test_simplify_ineq_constant_lt() {
        let c = Polynomial::constant(rat(5));
        let atom = IneqAtom::from_poly(c, AtomKind::Lt);

        let result = simplify_ineq_atom(&atom);
        // 5 < 0 is false
        assert!(matches!(result, Some(SimplifiedAtom::Trivial(false))));
    }

    #[test]
    fn test_eliminate_redundant_none() {
        let x = Polynomial::from_var(0);
        let y = Polynomial::from_var(1);

        let atoms = vec![
            Atom::Ineq(IneqAtom::from_poly(x, AtomKind::Gt)),
            Atom::Ineq(IneqAtom::from_poly(y, AtomKind::Lt)),
        ];

        let redundant = eliminate_redundant(&atoms);
        assert!(redundant.is_empty());
    }

    #[test]
    fn test_simplify_ineq_negative_leading_var_flips_kind() {
        // -x < 0  is equivalent to  x > 0, NOT  x < 0.
        let x = Polynomial::from_var(0);
        let neg_x = x.neg();
        let atom = IneqAtom::from_poly(neg_x, AtomKind::Lt);

        let result = simplify_ineq_atom(&atom);
        match result {
            Some(SimplifiedAtom::Atom(Atom::Ineq(simplified))) => {
                assert_eq!(simplified.kind, AtomKind::Gt);
                assert_eq!(simplified.factors.len(), 1);
                // The stored polynomial itself is canonicalized to +x.
                assert!(simplified.factors[0].poly.terms()[0].coeff.is_positive());
            }
            other => panic!("expected simplified Gt atom, got {other:?}"),
        }
    }

    #[test]
    fn test_simplify_ineq_negative_leading_var_gt_flips_to_lt() {
        // -x > 0  is equivalent to  x < 0.
        let x = Polynomial::from_var(0);
        let neg_x = x.neg();
        let atom = IneqAtom::from_poly(neg_x, AtomKind::Gt);

        let result = simplify_ineq_atom(&atom);
        match result {
            Some(SimplifiedAtom::Atom(Atom::Ineq(simplified))) => {
                assert_eq!(simplified.kind, AtomKind::Lt);
            }
            other => panic!("expected simplified Lt atom, got {other:?}"),
        }
    }

    #[test]
    fn test_simplify_ineq_negative_constant_single_factor_lt() {
        // (-5) < 0 is TRUE (not the same as 5 < 0, which is false).
        let c = Polynomial::constant(rat(-5));
        let atom = IneqAtom::from_poly(c, AtomKind::Lt);

        let result = simplify_ineq_atom(&atom);
        assert!(matches!(result, Some(SimplifiedAtom::Trivial(true))));
    }

    #[test]
    fn test_simplify_ineq_negative_constant_single_factor_gt() {
        // (-5) > 0 is FALSE.
        let c = Polynomial::constant(rat(-5));
        let atom = IneqAtom::from_poly(c, AtomKind::Gt);

        let result = simplify_ineq_atom(&atom);
        assert!(matches!(result, Some(SimplifiedAtom::Trivial(false))));
    }

    #[test]
    fn test_simplify_ineq_negative_constant_eq_unaffected() {
        // (-5) = 0 is FALSE, regardless of sign tracking.
        let c = Polynomial::constant(rat(-5));
        let atom = IneqAtom::from_poly(c, AtomKind::Eq);

        let result = simplify_ineq_atom(&atom);
        assert!(matches!(result, Some(SimplifiedAtom::Trivial(false))));
    }

    #[test]
    fn test_eliminate_redundant_duplicates() {
        let x = Polynomial::from_var(0);

        let atoms = vec![
            Atom::Ineq(IneqAtom::from_poly(x.clone(), AtomKind::Gt)),
            Atom::Ineq(IneqAtom::from_poly(x.clone(), AtomKind::Gt)),
            Atom::Ineq(IneqAtom::from_poly(x, AtomKind::Gt)),
        ];

        let redundant = eliminate_redundant(&atoms);
        assert_eq!(redundant.len(), 2); // Two duplicates found
        assert!(redundant.contains(&1));
        assert!(redundant.contains(&2));
    }
}
