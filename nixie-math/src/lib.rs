//! # nixie-math
//!
//! Mathematical foundations for the Nixie SMT solver.
//!
//! This crate provides Pure Rust implementations of mathematical algorithms
//! required for SMT solving, including:
//!
//! ## Linear Arithmetic
//! - **Simplex**: Dual simplex algorithm for linear programming (LRA theory)
//! - **Interior Point**: Primal-dual interior point method for large-scale LP
//! - **Matrix**: Dense and sparse matrix operations with Gaussian elimination
//! - **Interval**: Interval arithmetic for bound propagation
//! - **Delta Rational**: Support for strict inequalities in simplex
//! - **BLAS**: High-performance BLAS operations for large-scale LP (1000+ variables)
//!
//! ## Non-Linear Arithmetic
//! - **Polynomial**: Multivariate polynomial arithmetic with GCD and factorization
//! - **Rational Function**: Arithmetic on quotients of polynomials (p/q operations)
//! - **Gröbner**: Gröbner basis computation (Buchberger, F4, and F5 algorithms)
//! - **Real Closure**: Algebraic number representation and root isolation
//! - **Hilbert**: Hilbert basis computation for integer cones
//!
//! ## Decision Diagrams
//! - **BDD**: Reduced Ordered Binary Decision Diagrams
//! - **ZDD**: Zero-suppressed BDDs for sparse set representation
//! - **ADD**: Algebraic Decision Diagrams for rational-valued functions
//!
//! ## Numerical Utilities
//! - **Rational**: Arbitrary precision rational arithmetic utilities
//! - **MPFR**: Arbitrary precision floating-point arithmetic (MPFR-like)
//!
//! # Features
//!
//! - **`std`** (default): enables the standard library. Without it the crate
//!   builds as `no_std` + `alloc` (`just verify` builds this configuration
//!   with warnings denied). The following modules need floating-point or
//!   OS facilities that `core` does not provide and are therefore
//!   available only with `std`: [`blas`], [`blas_ops`], [`mpfr`],
//!   [`simd::matrix_simd`], [`simd::simplex_simd`], and
//!   [`rational::is_prime`] (which needs a random number generator).
//!   Everything else -- polynomials, Gröbner bases, simplex, intervals,
//!   BDDs, real closure, the transcendental enclosure -- builds in both
//!   configurations; the `std`-only `f64` methods it calls come from
//!   the `F64Ext` trait (exported without `std`, `libm` underneath), so a
//!   call site is written once.
//! - **`simd`**: reserved. The kernels in [`simd`] are compiled
//!   unconditionally and rely on auto-vectorization, so enabling this
//!   feature currently changes nothing; it exists so that an explicit
//!   opt-in does not become a breaking change later.
//!
//! # Examples
//!
//! ## Polynomial Arithmetic
//!
//! ```
//! use nixie_math::polynomial::{Polynomial, Var};
//!
//! // Create polynomial for variable x (index 0)
//! let x: Var = 0;
//!
//! // Create polynomial representing just x
//! let p = Polynomial::from_var(x);
//!
//! // Compute x * x = x^2
//! let p_squared = p.clone() * p.clone();
//! ```
//!
//! ## BDD Operations
//!
//! ```
//! use nixie_math::bdd::BddManager;
//!
//! let mut mgr = BddManager::new();
//!
//! // Create variables (VarId is u32)
//! let x = mgr.variable(0);
//! let y = mgr.variable(1);
//!
//! // Compute x AND y
//! let and_xy = mgr.and(x, y);
//!
//! // Compute x OR y
//! let or_xy = mgr.or(x, y);
//! ```
//!
//! ## BLAS Operations
//!
//! ```
//! use nixie_math::blas::{ddot, dgemv, Transpose};
//!
//! // Vector dot product
//! let x = vec![1.0, 2.0, 3.0];
//! let y = vec![4.0, 5.0, 6.0];
//! let dot = ddot(&x, &y);
//! assert_eq!(dot, 32.0);
//! ```
//!
//! ## Arbitrary Precision Floats
//!
//! ```
//! use nixie_math::mpfr::{ArbitraryFloat, Precision, RoundingMode};
//!
//! let prec = Precision::new(128);
//! let a = ArbitraryFloat::from_f64(3.14159, prec);
//! let b = ArbitraryFloat::from_f64(2.71828, prec);
//! let sum = a.add(&b, RoundingMode::RoundNearest);
//! ```

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

// Native builds must never silently end up on nixie-time's frozen stub clock
// (the `nixie-time/std` feature in this crate's manifest is what selects the
// real one; see nixie-time/src/lib.rs). The frozen clock is *by design* in the
// two configurations the cfg excludes: `no_std` (`--no-default-features`) and
// `wasm32-unknown-unknown`, which has no clock.
#[cfg(all(
    feature = "std",
    not(all(target_arch = "wasm32", target_os = "unknown"))
))]
const _: () = assert!(!nixie_time::IS_FROZEN, "nixie-time/std must be forwarded");

#[cfg(not(feature = "std"))]
extern crate alloc;

/// The `f64` methods that live in `std` rather than `core`, for `no_std` builds.
///
/// `core::f64` carries the comparisons, `abs`, `min`, `max`, `clamp`, the
/// bit-level operations and `is_*` class tests; the transcendental and
/// rounding methods – `sqrt`, `powi`, `exp`, `log10`, `floor`, `round`, … –
/// are inherent methods of `std`'s `f64` alone. This trait supplies them under
/// `#[cfg(not(feature = "std"))]` so that a call site is written once:
/// `use nixie_math::F64Ext;` and the method calls stay as they are. Under
/// `std` the trait does not exist and the inherent methods are used.
///
/// Each method is the corresponding `libm` routine, or a one-line
/// construction from one. The rounding methods and `sqrt` are fixed by IEEE
/// 754 (ties away from zero; correctly rounded), so the two configurations
/// agree bit for bit there; for the transcendental functions `libm` is the
/// musl implementation, within 1 ulp of the `std` result.
#[cfg(not(feature = "std"))]
pub trait F64Ext {
    /// `self` raised to an integer power, by squaring.
    fn powi(self, n: i32) -> f64;
    /// `self` raised to a floating-point power.
    fn powf(self, n: f64) -> f64;
    /// The correctly rounded square root.
    fn sqrt(self) -> f64;
    /// The cube root.
    fn cbrt(self) -> f64;
    /// *e* raised to `self`.
    fn exp(self) -> f64;
    /// *e* raised to `self`, minus one.
    fn exp_m1(self) -> f64;
    /// The natural logarithm.
    fn ln(self) -> f64;
    /// The natural logarithm of `1 + self`.
    fn ln_1p(self) -> f64;
    /// The logarithm of `self` with respect to `base`.
    fn log(self, base: f64) -> f64;
    /// The base-2 logarithm.
    fn log2(self) -> f64;
    /// The base-10 logarithm.
    fn log10(self) -> f64;
    /// The sine.
    fn sin(self) -> f64;
    /// The cosine.
    fn cos(self) -> f64;
    /// The tangent.
    fn tan(self) -> f64;
    /// The arcsine.
    fn asin(self) -> f64;
    /// The arccosine.
    fn acos(self) -> f64;
    /// The arctangent.
    fn atan(self) -> f64;
    /// The four-quadrant arctangent of `self` and `other`.
    fn atan2(self, other: f64) -> f64;
    /// The length of the hypotenuse with legs `self` and `other`.
    fn hypot(self, other: f64) -> f64;
    /// Fused multiply-add: `self * a + b`, rounded once.
    fn mul_add(self, a: f64, b: f64) -> f64;
    /// The smallest integer not less than `self`.
    fn ceil(self) -> f64;
    /// The largest integer not greater than `self`.
    fn floor(self) -> f64;
    /// The nearest integer, ties away from zero.
    fn round(self) -> f64;
    /// The integer part of `self`.
    fn trunc(self) -> f64;
    /// The fractional part of `self`.
    fn fract(self) -> f64;
    /// Euclidean division.
    fn div_euclid(self, rhs: f64) -> f64;
    /// The least non-negative remainder of Euclidean division.
    fn rem_euclid(self, rhs: f64) -> f64;
}

#[cfg(not(feature = "std"))]
impl F64Ext for f64 {
    fn powi(self, n: i32) -> f64 {
        // compiler-rt's `__powidf2`, which is what the `std` method lowers
        // to: exponentiation by squaring, the reciprocal taken at the end.
        let reciprocal = n < 0;
        let mut base = self;
        let mut exp = n;
        let mut acc = 1.0;
        loop {
            if exp & 1 != 0 {
                acc *= base;
            }
            exp /= 2;
            if exp == 0 {
                break;
            }
            base *= base;
        }
        if reciprocal { 1.0 / acc } else { acc }
    }

    fn powf(self, n: f64) -> f64 {
        libm::pow(self, n)
    }

    fn sqrt(self) -> f64 {
        libm::sqrt(self)
    }

    fn cbrt(self) -> f64 {
        libm::cbrt(self)
    }

    fn exp(self) -> f64 {
        libm::exp(self)
    }

    fn exp_m1(self) -> f64 {
        libm::expm1(self)
    }

    fn ln(self) -> f64 {
        libm::log(self)
    }

    fn ln_1p(self) -> f64 {
        libm::log1p(self)
    }

    fn log(self, base: f64) -> f64 {
        libm::log(self) / libm::log(base)
    }

    fn log2(self) -> f64 {
        libm::log2(self)
    }

    fn log10(self) -> f64 {
        libm::log10(self)
    }

    fn sin(self) -> f64 {
        libm::sin(self)
    }

    fn cos(self) -> f64 {
        libm::cos(self)
    }

    fn tan(self) -> f64 {
        libm::tan(self)
    }

    fn asin(self) -> f64 {
        libm::asin(self)
    }

    fn acos(self) -> f64 {
        libm::acos(self)
    }

    fn atan(self) -> f64 {
        libm::atan(self)
    }

    fn atan2(self, other: f64) -> f64 {
        libm::atan2(self, other)
    }

    fn hypot(self, other: f64) -> f64 {
        libm::hypot(self, other)
    }

    fn mul_add(self, a: f64, b: f64) -> f64 {
        libm::fma(self, a, b)
    }

    fn ceil(self) -> f64 {
        libm::ceil(self)
    }

    fn floor(self) -> f64 {
        libm::floor(self)
    }

    fn round(self) -> f64 {
        libm::round(self)
    }

    fn trunc(self) -> f64 {
        libm::trunc(self)
    }

    fn fract(self) -> f64 {
        self - self.trunc()
    }

    fn div_euclid(self, rhs: f64) -> f64 {
        let q = (self / rhs).trunc();
        if self % rhs < 0.0 {
            return if rhs > 0.0 { q - 1.0 } else { q + 1.0 };
        }
        q
    }

    fn rem_euclid(self, rhs: f64) -> f64 {
        let r = self % rhs;
        if r < 0.0 { r + rhs.abs() } else { r }
    }
}

mod prelude;

pub mod algebraic;
pub mod bdd;
#[cfg(feature = "std")]
pub mod blas;
#[cfg(feature = "std")]
pub mod blas_ops;
pub mod delta_rational;
pub mod fast_rational;
pub mod ff;
pub mod grobner;
pub mod hilbert;
pub mod interior_point;
pub mod interval;
pub mod lp;
pub mod lp_core;
pub mod matrix;
#[cfg(feature = "std")]
pub mod mpfr;
pub mod polynomial;
pub mod rational;
pub mod rational_function;
pub mod realclosure;
pub mod realclosure_advanced;
pub mod simd;
pub mod simplex;
pub mod simplex_parametric;
pub mod simplex_solver;
pub mod transcendental;

pub use simplex_solver::{
    Constraint as SimplexConstraint, ConstraintKind, SimplexError, SimplexSolver, SolveResult,
    SolveStatus,
};

#[cfg(test)]
mod integration_tests {
    use super::*;
    use num_bigint::BigInt;
    use num_rational::BigRational;

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(n))
    }

    #[test]
    fn test_grobner_with_root_isolation() {
        // Integration test: Use Gröbner basis to simplify, then isolate roots
        // System: x^2 - 2 = 0, y - x = 0
        // Should reduce to y^2 - 2 = 0

        let x_squared_minus_2 = polynomial::Polynomial::from_coeffs_int(&[
            (1, &[(0, 2)]), // x^2
            (-2, &[]),      // -2
        ]);

        let y_minus_x = polynomial::Polynomial::from_coeffs_int(&[
            (1, &[(1, 1)]),  // y
            (-1, &[(0, 1)]), // -x
        ]);

        let gb =
            grobner::grobner_basis(&[x_squared_minus_2.clone(), y_minus_x]).expect("completes");

        // The Gröbner basis should contain polynomials
        assert!(!gb.is_empty());

        // One of the polynomials should be univariate
        let has_univariate = gb.iter().any(|p| p.is_univariate());
        assert!(has_univariate || gb.len() == 1);
    }

    #[test]
    fn test_nra_solver_with_algebraic_numbers() {
        // Integration test: NRA solver with algebraic number evaluation
        // Solve x^2 - 2 = 0

        let mut solver = grobner::NraSolver::new();

        let x_squared_minus_2 = polynomial::Polynomial::from_coeffs_int(&[
            (1, &[(0, 2)]), // x^2
            (-2, &[]),      // -2
        ]);

        solver.add_equality(x_squared_minus_2.clone());

        // Should be satisfiable
        assert_eq!(solver.check_sat(), grobner::SatResult::Sat);

        // Create algebraic number for sqrt(2)
        // AlgebraicNumber::new(poly, var, lower, upper)
        let sqrt_2 = realclosure::AlgebraicNumber::new(
            x_squared_minus_2,
            0, // variable 0
            rat(1),
            rat(2),
        );

        // Algebraic number should be valid
        let _ = sqrt_2;
    }

    #[test]
    fn test_interval_with_polynomial_bounds() {
        // Integration test: Use interval arithmetic with polynomial evaluation
        // Evaluate x^2 over [1, 2] should give [1, 4]

        let x_squared = polynomial::Polynomial::from_coeffs_int(&[(1, &[(0, 2)])]);

        // Evaluate at x = 1
        let mut assignment1 = crate::prelude::FxHashMap::default();
        assignment1.insert(0, rat(1));
        let val1 = x_squared.eval(&assignment1);
        assert_eq!(val1, rat(1));

        // Evaluate at x = 2
        let mut assignment2 = crate::prelude::FxHashMap::default();
        assignment2.insert(0, rat(2));
        let val2 = x_squared.eval(&assignment2);
        assert_eq!(val2, rat(4));

        // Create interval [1, 4]
        let interval = interval::Interval::closed(rat(1), rat(4));
        assert!(interval.contains(&val1));
        assert!(interval.contains(&val2));
    }

    #[test]
    fn test_delta_rationals_ordering() {
        // Integration test: Delta rationals for strict inequalities
        let delta_zero = delta_rational::DeltaRational::from_rational(rat(0));
        let delta_small = delta_rational::DeltaRational::new(rat(0), 1); // delta_coeff is i64

        // 0 + delta > 0
        assert!(delta_small > delta_zero);

        // Delta rationals maintain ordering
        let delta_one = delta_rational::DeltaRational::from_rational(rat(1));
        assert!(delta_one > delta_small);
    }

    #[test]
    fn test_matrix_operations() {
        // Integration test: Matrix operations (used in F4 algorithm)
        use matrix::Matrix;
        use num_rational::Rational64;

        // Create a simple 2x2 matrix
        let m = Matrix::from_vec(
            2,
            2,
            vec![
                Rational64::new(2, 1),
                Rational64::new(1, 1),
                Rational64::new(1, 1),
                Rational64::new(1, 1),
            ],
        );

        // Check matrix values
        assert_eq!(m.get(0, 0), Rational64::new(2, 1));
        assert_eq!(m.get(0, 1), Rational64::new(1, 1));
    }

    #[test]
    fn test_polynomial_factorization_with_grobner() {
        // Integration test: Factorization helps with Gröbner basis computation
        // x^2 - y^2 can be analyzed via Gröbner basis

        let x_sq_minus_y_sq = polynomial::Polynomial::from_coeffs_int(&[
            (1, &[(0, 2)]),  // x^2
            (-1, &[(1, 2)]), // -y^2
        ]);

        // Compute Gröbner basis of {x^2 - y^2}
        let gb = grobner::grobner_basis(&[x_sq_minus_y_sq]).expect("completes");

        assert!(!gb.is_empty());
    }

    #[test]
    fn test_real_closure_root_isolation_integration() {
        // Integration test: Real closure and root isolation
        // Find roots of x^3 - 2 = 0

        let poly = polynomial::Polynomial::from_coeffs_int(&[
            (1, &[(0, 3)]), // x^3
            (-2, &[]),      // -2
        ]);

        // Isolate roots (for variable 0)
        let roots = poly.isolate_roots(0);

        // Should find at least one real root (cube root of 2)
        assert!(!roots.is_empty());
    }

    #[test]
    fn test_polynomial_gcd_univariate() {
        // Integration test: GCD computation for univariate polynomials
        // gcd(x^2 - 1, x - 1) = x - 1

        let p1 = polynomial::Polynomial::from_coeffs_int(&[
            (1, &[(0, 2)]), // x^2
            (-1, &[]),      // -1
        ]);

        let p2 = polynomial::Polynomial::from_coeffs_int(&[
            (1, &[(0, 1)]), // x
            (-1, &[]),      // -1
        ]);

        let gcd = p1.gcd_univariate(&p2);

        // GCD should be x - 1 (or a scalar multiple)
        assert_eq!(gcd.total_degree(), 1);
    }
}
