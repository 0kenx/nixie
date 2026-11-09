//! Exact arithmetic in rational algebraic extensions.
//!
//! A caller supplies a nonconstant defining polynomial, irreducible for a field.
//! The same operations also define quotient-algebra arithmetic for reducible
//! polynomials; inversion then fails for nonunits. No irreducibility is inferred.

#[allow(unused_imports)]
use crate::prelude::*;
use num_rational::BigRational;
use num_traits::{One, Zero};

/// Invalid defining-polynomial state.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum FieldExtensionError {
    /// A zero or constant polynomial cannot define an algebraic extension.
    #[error("the defining polynomial must have positive degree")]
    InvalidPolynomial,
    /// The public degree was changed inconsistently with the defining polynomial.
    #[error("extension degree does not match the defining polynomial")]
    InconsistentDegree,
}

/// Coefficients of a polynomial in the generator of an extension.
#[derive(Clone, Debug)]
pub struct FieldElement {
    /// Coefficients in ascending order of powers of the generator.
    pub coeffs: Vec<BigRational>,
    /// Zero denotes the rational field; other IDs belong to a manager.
    pub extension_id: ExtensionId,
}

/// Manager-local identifier; zero is reserved for the rational field.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ExtensionId(pub usize);

/// The rational quotient algebra defined by a nonconstant polynomial.
///
/// For an irreducible polynomial this is a field. Fields remain public for API
/// compatibility, but modifying them requires preserving [`Self::validate`].
/// Infallible arithmetic methods panic on invalid state rather than fabricate a
/// value; fallible inversion and manager operations decline invalid state.
#[derive(Clone, Debug)]
pub struct FieldExtension {
    /// Defining polynomial, with coefficients in ascending power order.
    pub minimal_poly: Vec<BigRational>,
    /// Degree of the defining polynomial, ignoring trailing zeros.
    pub degree: usize,
}

fn normalized(mut coefficients: Vec<BigRational>) -> Vec<BigRational> {
    while coefficients.last().is_some_and(Zero::is_zero) {
        coefficients.pop();
    }
    if coefficients.is_empty() {
        coefficients.push(BigRational::zero());
    }
    coefficients
}

fn require_valid<T>(value: Result<T, FieldExtensionError>) -> T {
    match value {
        Ok(value) => value,
        Err(error) => panic!("invalid field extension: {error}"),
    }
}

impl FieldExtension {
    /// Construct an extension, rejecting zero and constant defining polynomials.
    pub fn try_new(minimal_poly: Vec<BigRational>) -> Result<Self, FieldExtensionError> {
        let minimal_poly = normalized(minimal_poly);
        if minimal_poly.len() < 2 {
            return Err(FieldExtensionError::InvalidPolynomial);
        }
        Ok(Self {
            degree: minimal_poly.len() - 1,
            minimal_poly,
        })
    }

    /// Construct an extension. The caller supplies an irreducible polynomial
    /// when field (rather than quotient-algebra) semantics are required.
    ///
    /// # Panics
    /// Panics for a zero or constant polynomial; use [`Self::try_new`] to handle
    /// invalid input as an error.
    pub fn new(minimal_poly: Vec<BigRational>) -> Self {
        require_valid(Self::try_new(minimal_poly))
    }

    /// Validate the defining polynomial and its public degree metadata.
    pub fn validate(&self) -> Result<(), FieldExtensionError> {
        self.modulus().map(|_| ())
    }

    fn modulus(&self) -> Result<&[BigRational], FieldExtensionError> {
        let degree = self
            .minimal_poly
            .iter()
            .rposition(|c| !c.is_zero())
            .filter(|&degree| degree > 0)
            .ok_or(FieldExtensionError::InvalidPolynomial)?;
        if degree != self.degree {
            return Err(FieldExtensionError::InconsistentDegree);
        }
        Ok(&self.minimal_poly[..=degree])
    }

    /// Whether the actual leading coefficient of a valid defining polynomial is one.
    pub fn is_monic(&self) -> bool {
        self.modulus()
            .is_ok_and(|p| p.last().is_some_and(One::is_one))
    }

    /// Reduce coefficients modulo the defining polynomial.
    ///
    /// # Panics
    /// Panics if public state no longer satisfies [`Self::validate`].
    pub fn reduce(&self, coeffs: &[BigRational]) -> Vec<BigRational> {
        let modulus = require_valid(self.modulus());
        require_valid(poly_div(coeffs, modulus)).1
    }

    /// Multiply and reduce two elements. Panics on invalid extension state.
    pub fn multiply(&mut self, a: &[BigRational], b: &[BigRational]) -> Vec<BigRational> {
        self.reduce(&poly_mult(a, b))
    }

    /// Add and reduce two elements. Panics on invalid extension state.
    pub fn add(&self, a: &[BigRational], b: &[BigRational]) -> Vec<BigRational> {
        let mut sum = vec![BigRational::zero(); a.len().max(b.len())];
        for (i, coefficient) in a.iter().enumerate() {
            sum[i] += coefficient;
        }
        for (i, coefficient) in b.iter().enumerate() {
            sum[i] += coefficient;
        }
        self.reduce(&sum)
    }

    /// Negate and reduce an element. Panics on invalid extension state.
    pub fn negate(&self, a: &[BigRational]) -> Vec<BigRational> {
        self.reduce(&a.iter().map(|coefficient| -coefficient).collect::<Vec<_>>())
    }

    /// Invert a unit by iterative polynomial extended Euclid.
    /// Returns `None` for nonunits or invalid extension state.
    pub fn inverse(&mut self, a: &[BigRational]) -> Option<Vec<BigRational>> {
        let modulus = self.modulus().ok()?;
        let mut old_r = poly_div(a, modulus).ok()?.1;
        let mut r = modulus.to_vec();
        let mut old_s = vec![BigRational::one()];
        let mut s = vec![BigRational::zero()];
        while r.iter().any(|c| !c.is_zero()) {
            let (quotient, remainder) = poly_div(&old_r, &r).ok()?;
            let next_s = poly_sub(&old_s, &poly_mult(&quotient, &s));
            old_r = core::mem::replace(&mut r, remainder);
            old_s = core::mem::replace(&mut s, next_s);
        }
        let [constant] = old_r.as_slice() else {
            return None;
        };
        if constant.is_zero() {
            return None;
        }
        let inverse = self.reduce(&old_s.iter().map(|c| c / constant).collect::<Vec<_>>());
        // Check the original operand, independently of the Euclidean updates.
        (self.reduce(&poly_mult(a, &inverse)) == vec![BigRational::one()]).then_some(inverse)
    }

    /// Matrix of multiplication by `a` in the basis 1, alpha, ..., alpha^(n-1).
    // Iterate columns of a row-major matrix: iterating its rows instead would
    // transpose the linear operator and obscure the basis convention.
    #[allow(clippy::needless_range_loop)]
    fn multiplication_matrix(&self, a: &[BigRational]) -> Vec<Vec<BigRational>> {
        require_valid(self.validate());
        let mut matrix = vec![vec![BigRational::zero(); self.degree]; self.degree];
        let mut column = self.reduce(a);
        for j in 0..self.degree {
            for (i, coefficient) in column.iter().enumerate() {
                matrix[i][j] = coefficient.clone();
            }
            column.insert(0, BigRational::zero());
            column = self.reduce(&column);
        }
        matrix
    }

    /// Exact norm: determinant of multiplication by the element.
    /// Panics on invalid extension state.
    pub fn norm(&mut self, a: &[BigRational]) -> BigRational {
        determinant(self.multiplication_matrix(a))
    }

    /// Exact trace: trace of multiplication by the element.
    /// Panics on invalid extension state.
    pub fn trace(&self, a: &[BigRational]) -> BigRational {
        self.multiplication_matrix(a)
            .iter()
            .enumerate()
            .fold(BigRational::zero(), |sum, (i, row)| sum + &row[i])
    }

    /// Whether 1, a, ..., a^(n-1) span the algebra over Q.
    /// For a field this is exactly whether `a` is a primitive element.
    /// Panics on invalid extension state.
    // Each successive power supplies a column, not a row.
    #[allow(clippy::needless_range_loop)]
    pub fn is_primitive(&mut self, a: &[BigRational]) -> bool {
        require_valid(self.validate());
        let a = self.reduce(a);
        let mut powers = vec![vec![BigRational::zero(); self.degree]; self.degree];
        let mut power = vec![BigRational::one()];
        for j in 0..self.degree {
            for (i, coefficient) in power.iter().enumerate() {
                powers[i][j] = coefficient.clone();
            }
            power = self.reduce(&poly_mult(&power, &a));
        }
        !determinant(powers).is_zero()
    }
}

/// Normalized polynomial long division over Q. Trimming at every iteration is
/// essential: cancellation can remove several leading terms in one step.
fn poly_div(
    a: &[BigRational],
    b: &[BigRational],
) -> Result<(Vec<BigRational>, Vec<BigRational>), FieldExtensionError> {
    let divisor = normalized(b.to_vec());
    let Some(leading) = divisor.last().filter(|c| !c.is_zero()) else {
        return Err(FieldExtensionError::InvalidPolynomial);
    };
    let mut remainder = normalized(a.to_vec());
    let mut quotient = vec![BigRational::zero(); remainder.len().saturating_sub(divisor.len()) + 1];
    while remainder.len() >= divisor.len() && remainder.iter().any(|c| !c.is_zero()) {
        let offset = remainder.len() - divisor.len();
        let top = remainder
            .last()
            .ok_or(FieldExtensionError::InvalidPolynomial)?;
        let coefficient = top / leading;
        quotient[offset] += &coefficient;
        for (i, value) in divisor.iter().enumerate() {
            remainder[offset + i] -= &coefficient * value;
        }
        remainder = normalized(remainder);
    }
    Ok((normalized(quotient), remainder))
}

fn poly_mult(a: &[BigRational], b: &[BigRational]) -> Vec<BigRational> {
    if a.is_empty() || b.is_empty() {
        return vec![BigRational::zero()];
    }
    let mut result = vec![BigRational::zero(); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        for (j, y) in b.iter().enumerate() {
            result[i + j] += x * y;
        }
    }
    normalized(result)
}

fn poly_sub(a: &[BigRational], b: &[BigRational]) -> Vec<BigRational> {
    let mut result = vec![BigRational::zero(); a.len().max(b.len())];
    for (i, value) in a.iter().enumerate() {
        result[i] += value;
    }
    for (i, value) in b.iter().enumerate() {
        result[i] -= value;
    }
    normalized(result)
}

/// Exact rational Gaussian elimination. Row subtraction preserves determinant;
/// a pivot swap changes its sign; a missing pivot proves determinant zero.
fn determinant(mut matrix: Vec<Vec<BigRational>>) -> BigRational {
    let mut result = BigRational::one();
    for column in 0..matrix.len() {
        let Some(pivot) = (column..matrix.len()).find(|&i| !matrix[i][column].is_zero()) else {
            return BigRational::zero();
        };
        if pivot != column {
            matrix.swap(pivot, column);
            result = -result;
        }
        let pivot_value = matrix[column][column].clone();
        result *= &pivot_value;
        let (upper, lower) = matrix.split_at_mut(column + 1);
        let pivot_row = &upper[column];
        for row in lower {
            let factor = &row[column] / &pivot_value;
            for j in column + 1..row.len() {
                row[j] -= &factor * &pivot_row[j];
            }
            row[column] = BigRational::zero();
        }
    }
    result
}

impl FieldElement {
    /// Construct an element, normalizing its coefficient representation.
    pub fn new(coeffs: Vec<BigRational>, extension_id: ExtensionId) -> Self {
        Self {
            coeffs: normalized(coeffs),
            extension_id,
        }
    }
    /// Construct an element of Q, whose reserved extension ID is zero.
    pub fn from_rational(r: BigRational) -> Self {
        Self::new(vec![r], ExtensionId(0))
    }
    /// Whether this polynomial representation is constant (including empty zero).
    pub fn is_rational(&self) -> bool {
        self.coeffs.iter().skip(1).all(Zero::is_zero)
    }
    /// Constant coefficient, with the empty polynomial interpreted as zero.
    pub fn rational_part(&self) -> BigRational {
        self.coeffs
            .first()
            .cloned()
            .unwrap_or_else(BigRational::zero)
    }
    /// Highest nonzero exponent; zero has degree zero by this API's convention.
    pub fn degree(&self) -> usize {
        self.coeffs.iter().rposition(|c| !c.is_zero()).unwrap_or(0)
    }
}

/// Manager of non-rational extension IDs; zero remains reserved for Q.
pub struct FieldExtensionManager {
    extensions: Vec<FieldExtension>,
}

impl FieldExtensionManager {
    /// Construct an empty manager.
    pub fn new() -> Self {
        Self {
            extensions: Vec::new(),
        }
    }

    /// Intern a defining polynomial up to a nonzero rational scalar.
    ///
    /// The lookup examines current defining polynomials because callers can
    /// mutate extensions through [`Self::get_extension`]. Cached polynomial-to-ID
    /// maps would otherwise return IDs belonging to a different polynomial.
    /// Panics for zero or constant polynomials.
    pub fn get_or_create(&mut self, minimal_poly: Vec<BigRational>) -> ExtensionId {
        let extension = FieldExtension::new(minimal_poly);
        let monic = |p: &[BigRational]| -> Result<Vec<BigRational>, FieldExtensionError> {
            let lead = p
                .last()
                .filter(|c| !c.is_zero())
                .ok_or(FieldExtensionError::InvalidPolynomial)?;
            Ok(p.iter().map(|c| c / lead).collect())
        };
        let key = require_valid(extension.modulus().and_then(monic));
        for (index, existing) in self.extensions.iter().enumerate() {
            if existing.modulus().and_then(monic).is_ok_and(|p| p == key) {
                return ExtensionId(index + 1);
            }
        }
        self.extensions.push(extension);
        ExtensionId(self.extensions.len())
    }

    /// Access a registered extension. Zero denotes Q and has no mutable entry.
    pub fn get_extension(&mut self, id: ExtensionId) -> Option<&mut FieldExtension> {
        self.extensions.get_mut(id.0.checked_sub(1)?)
    }

    /// Add two elements in the same field.
    pub fn add(&mut self, a: &FieldElement, b: &FieldElement) -> Option<FieldElement> {
        if a.extension_id != b.extension_id {
            return None;
        }
        if a.extension_id == ExtensionId(0) {
            return (a.is_rational() && b.is_rational())
                .then(|| FieldElement::from_rational(a.rational_part() + b.rational_part()));
        }
        let ext = self.get_extension(a.extension_id)?;
        ext.validate().ok()?;
        Some(FieldElement::new(
            ext.add(&a.coeffs, &b.coeffs),
            a.extension_id,
        ))
    }

    /// Multiply two elements in the same field.
    pub fn multiply(&mut self, a: &FieldElement, b: &FieldElement) -> Option<FieldElement> {
        if a.extension_id != b.extension_id {
            return None;
        }
        if a.extension_id == ExtensionId(0) {
            return (a.is_rational() && b.is_rational())
                .then(|| FieldElement::from_rational(a.rational_part() * b.rational_part()));
        }
        let ext = self.get_extension(a.extension_id)?;
        ext.validate().ok()?;
        Some(FieldElement::new(
            ext.multiply(&a.coeffs, &b.coeffs),
            a.extension_id,
        ))
    }

    /// Invert an element; nonunits and invalid field state return `None`.
    pub fn inverse(&mut self, a: &FieldElement) -> Option<FieldElement> {
        if a.extension_id == ExtensionId(0) {
            let rational = a.rational_part();
            return (a.is_rational() && !rational.is_zero())
                .then(|| FieldElement::from_rational(rational.recip()));
        }
        let coeffs = self.get_extension(a.extension_id)?.inverse(&a.coeffs)?;
        Some(FieldElement::new(coeffs, a.extension_id))
    }

    /// Exact field norm, or `None` for invalid field state.
    pub fn norm(&mut self, a: &FieldElement) -> Option<BigRational> {
        if a.extension_id == ExtensionId(0) {
            return a.is_rational().then(|| a.rational_part());
        }
        let ext = self.get_extension(a.extension_id)?;
        ext.validate().ok()?;
        Some(ext.norm(&a.coeffs))
    }

    /// Exact field trace, or `None` for invalid field state.
    pub fn trace(&mut self, a: &FieldElement) -> Option<BigRational> {
        if a.extension_id == ExtensionId(0) {
            return a.is_rational().then(|| a.rational_part());
        }
        let ext = self.get_extension(a.extension_id)?;
        ext.validate().ok()?;
        Some(ext.trace(&a.coeffs))
    }
}

impl Default for FieldExtensionManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(n))
    }

    #[test]
    fn reduction_and_division_remove_all_cancelled_leading_terms() {
        let mut extension = FieldExtension::new(vec![rat(-2), rat(0), rat(1), rat(0)]);
        assert_eq!(extension.degree, 2);
        assert_eq!(
            extension.reduce(&[rat(0), rat(0), rat(0), rat(0), rat(1), rat(0)]),
            vec![rat(4)]
        );
        assert_eq!(extension.add(&[rat(0), rat(0), rat(1)], &[]), vec![rat(2)]);
        assert_eq!(extension.negate(&[rat(0), rat(0), rat(1)]), vec![rat(-2)]);
        assert_eq!(extension.multiply(&[], &[]), vec![rat(0)]);
        let (q, r) = poly_div(
            &[rat(1), rat(0), rat(0), rat(0), rat(1)],
            &[rat(-2), rat(0), rat(1), rat(0)],
        )
        .expect("division");
        assert_eq!(q, vec![rat(2), rat(0), rat(1)]);
        assert_eq!(r, vec![rat(5)]);
        assert!(poly_div(&[rat(1)], &[rat(0), rat(0)]).is_err());
    }

    #[test]
    fn norm_and_trace_use_every_coefficient_and_nonmonic_moduli() {
        // alpha^2 - alpha - 1 = 0: Tr(alpha)=1, N(alpha)=-1.
        let mut extension = FieldExtension::new(vec![rat(-2), rat(-2), rat(2)]);
        assert!(!extension.is_monic());
        assert_eq!(extension.trace(&[rat(0), rat(1)]), rat(1));
        assert_eq!(extension.norm(&[rat(0), rat(1)]), rat(-1));
        assert_eq!(extension.trace(&[rat(1), rat(1)]), rat(3));
        assert_eq!(extension.norm(&[rat(1), rat(1)]), rat(1));
        assert_eq!(extension.trace(&[rat(0), rat(0), rat(1)]), rat(3));
        assert_eq!(extension.norm(&[rat(0), rat(0), rat(1)]), rat(1));
        let huge = BigRational::from_integer(BigInt::from(1u8) << 160usize);
        assert_eq!(extension.norm(core::slice::from_ref(&huge)), &huge * &huge);
        assert_eq!(
            extension.trace(core::slice::from_ref(&huge)),
            &huge * rat(2)
        );
        assert_eq!(extension.norm(&[]), rat(0));
    }

    #[test]
    fn primitive_element_requires_a_full_power_basis() {
        // x^4 - 2 is irreducible (Eisenstein); alpha^2 lies in a degree-two subfield.
        let mut extension = FieldExtension::new(vec![rat(-2), rat(0), rat(0), rat(0), rat(1)]);
        assert!(extension.is_primitive(&[rat(0), rat(1)]));
        assert!(!extension.is_primitive(&[rat(0), rat(0), rat(1), rat(0)]));
        assert!(!extension.is_primitive(&[rat(3), rat(0), rat(0), rat(0)]));
        assert!(FieldExtension::new(vec![rat(-3), rat(1)]).is_primitive(&[]));
    }

    #[test]
    fn inverse_and_manager_lookup_follow_mutated_moduli() {
        let mut extension = FieldExtension::new(vec![rat(-2), rat(0), rat(1)]);
        assert_eq!(
            extension.inverse(&[rat(0), rat(1)]),
            Some(vec![rat(0), BigRational::new(1.into(), 2.into())])
        );
        extension.minimal_poly[0] = rat(-3);
        assert_eq!(
            extension.inverse(&[rat(0), rat(1)]),
            Some(vec![rat(0), BigRational::new(1.into(), 3.into())])
        );
        extension.degree = 7;
        assert_eq!(
            extension.validate(),
            Err(FieldExtensionError::InconsistentDegree)
        );
        assert!(extension.inverse(&[rat(1)]).is_none());
        let mut manager = FieldExtensionManager::new();
        let first = manager.get_or_create(vec![rat(-2), rat(0), rat(1)]);
        assert_ne!(first, ExtensionId(0));
        manager
            .get_extension(first)
            .expect("extension")
            .minimal_poly[0] = rat(-3);
        let second = manager.get_or_create(vec![rat(-2), rat(0), rat(1)]);
        assert_ne!(first, second);
        assert_eq!(
            second,
            manager.get_or_create(vec![rat(-4), rat(0), rat(2), rat(0)])
        );
        manager
            .get_extension(first)
            .expect("extension")
            .minimal_poly
            .clear();
        assert!(
            manager
                .norm(&FieldElement::new(vec![rat(1)], first))
                .is_none()
        );
    }

    #[test]
    fn invalid_moduli_and_rational_field_are_distinct() {
        for polynomial in [vec![], vec![rat(0)], vec![rat(5)], vec![rat(0), rat(0)]] {
            assert!(matches!(
                FieldExtension::try_new(polynomial),
                Err(FieldExtensionError::InvalidPolynomial)
            ));
        }
        let mut manager = FieldExtensionManager::new();
        let a = FieldElement::from_rational(rat(2));
        let b = FieldElement::from_rational(rat(3));
        assert_eq!(
            manager.add(&a, &b).expect("Q addition").coeffs,
            vec![rat(5)]
        );
        assert_eq!(
            manager.multiply(&a, &b).expect("Q multiplication").coeffs,
            vec![rat(6)]
        );
        assert_eq!(manager.norm(&a), Some(rat(2)));
        assert_eq!(manager.trace(&a), Some(rat(2)));
        assert_eq!(
            manager.inverse(&a).expect("Q inverse").coeffs,
            vec![BigRational::new(1.into(), 2.into())]
        );
        assert!(
            manager
                .inverse(&FieldElement::from_rational(rat(0)))
                .is_none()
        );
        assert!(manager.get_extension(ExtensionId(0)).is_none());
        let empty = FieldElement {
            coeffs: vec![],
            extension_id: ExtensionId(0),
        };
        assert!(empty.is_rational());
        assert_eq!(manager.norm(&empty), Some(rat(0)));
    }

    #[test]
    fn exact_arithmetic_identities_hold_beyond_quadratic_fields() {
        // x^3 - 2 is irreducible; all nonzero representatives are units.
        let mut extension = FieldExtension::new(vec![rat(-2), rat(0), rat(0), rat(1)]);
        assert_eq!(extension.norm(&[rat(0), rat(1)]), rat(2));
        assert_eq!(extension.trace(&[rat(0), rat(1)]), rat(0));
        for constant in -3..=3 {
            for coefficient in -3..=3 {
                // Product over the three conjugates of alpha, alpha^3 = 2.
                let a = [rat(constant), rat(coefficient)];
                assert_eq!(
                    extension.norm(&a),
                    rat(constant.pow(3) + 2 * coefficient.pow(3))
                );
                assert_eq!(extension.trace(&a), rat(3 * constant));
            }
        }
        for a0 in -2..=2 {
            for a1 in -2..=2 {
                for a2 in -2..=2 {
                    let a = vec![rat(a0), rat(a1), rat(a2), rat(0)];
                    if a.iter().all(Zero::is_zero) {
                        assert!(extension.inverse(&a).is_none());
                        continue;
                    }
                    let inverse = extension.inverse(&a).expect("nonzero field element");
                    assert_eq!(extension.multiply(&a, &inverse), vec![rat(1)]);
                    assert_eq!(extension.norm(&a) * extension.norm(&inverse), rat(1));
                    let b = [rat(1), rat(-1)];
                    let product = extension.multiply(&a, &b);
                    assert_eq!(
                        extension.norm(&product),
                        extension.norm(&a) * extension.norm(&b)
                    );
                    let sum = extension.add(&a, &b);
                    assert_eq!(
                        extension.trace(&sum),
                        extension.trace(&a) + extension.trace(&b)
                    );
                }
            }
        }
        let mut quotient = FieldExtension::new(vec![rat(-1), rat(0), rat(1)]);
        assert!(quotient.inverse(&[rat(-1), rat(1)]).is_none());
        assert_eq!(quotient.norm(&[rat(-1), rat(1)]), rat(0));
    }

    #[test]
    fn long_division_has_a_strictly_smaller_remainder_and_reconstructs_input() {
        for degree in 1..=9 {
            for gap in 0..=5 {
                let mut divisor = vec![rat(0); degree + 3];
                divisor[0] = rat(-3);
                divisor[degree] = BigRational::new(2.into(), 3.into());
                let mut dividend = vec![rat(0); degree + gap + 4];
                dividend[0] = rat(7);
                dividend[degree + gap] = BigRational::new(5.into(), 7.into());
                let (quotient, remainder) = poly_div(&dividend, &divisor).expect("division");
                assert!(remainder.len() <= degree);
                let product = poly_mult(&quotient, &divisor);
                let negative_remainder: Vec<_> = remainder.iter().map(|x| -x).collect();
                assert_eq!(
                    poly_sub(&product, &negative_remainder),
                    normalized(dividend)
                );
            }
        }
    }

    #[test]
    fn test_field_extension_creation() {
        // Create Q(√2) via minimal polynomial x² - 2
        let minimal_poly = vec![rat(-2), rat(0), rat(1)]; // -2 + 0x + x²
        let ext = FieldExtension::new(minimal_poly);

        assert_eq!(ext.degree, 2);
        assert!(ext.is_monic());
    }

    #[test]
    fn test_reduction() {
        // Q(√2): x² - 2 = 0, so x² ≡ 2
        let minimal_poly = vec![rat(-2), rat(0), rat(1)];
        let ext = FieldExtension::new(minimal_poly);

        // Reduce x² to 2
        let reduced = ext.reduce(&[rat(0), rat(0), rat(1)]);
        assert_eq!(reduced, vec![rat(2)]);
    }

    #[test]
    fn test_multiplication() {
        // Q(√2): x² = 2
        let minimal_poly = vec![rat(-2), rat(0), rat(1)];
        let mut ext = FieldExtension::new(minimal_poly);

        // (1 + √2) * (1 + √2) = 1 + 2√2 + 2 = 3 + 2√2
        let a = vec![rat(1), rat(1)]; // 1 + x
        let b = vec![rat(1), rat(1)]; // 1 + x

        let product = ext.multiply(&a, &b);
        assert_eq!(product, vec![rat(3), rat(2)]);
    }

    #[test]
    fn test_field_element_manager() {
        let mut mgr = FieldExtensionManager::new();

        // Create Q(√2)
        let minimal_poly = vec![rat(-2), rat(0), rat(1)];
        let ext_id = mgr.get_or_create(minimal_poly);

        // Create elements 1 + √2 and 2 + √2
        let a = FieldElement::new(vec![rat(1), rat(1)], ext_id);
        let b = FieldElement::new(vec![rat(2), rat(1)], ext_id);

        // Add them: should get 3 + 2√2
        let sum = mgr.add(&a, &b).expect("addition failed");
        assert_eq!(sum.coeffs, vec![rat(3), rat(2)]);
    }

    #[test]
    fn test_inverse() {
        // Q(√2): x² = 2
        let minimal_poly = vec![rat(-2), rat(0), rat(1)];
        let mut ext = FieldExtension::new(minimal_poly);

        // Inverse of 1 + √2 is (-1 + √2) / (-1) = (√2 - 1)
        let a = vec![rat(1), rat(1)];
        let inv = ext.inverse(&a).expect("inverse should exist");

        // Check: (1 + √2) * inv = 1
        let product = ext.multiply(&a, &inv);
        assert_eq!(product, vec![rat(1)]);
    }
}
