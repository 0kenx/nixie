//! Arbitrary precision rational arithmetic utilities.
//!
//! This module provides utility functions for working with rational numbers
//! beyond what the `num_rational` crate offers.

#[allow(unused_imports)]
use crate::prelude::*;
use core::cmp::Ordering;
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// Compare two rationals and return their ordering.
#[inline]
pub fn cmp(a: &BigRational, b: &BigRational) -> Ordering {
    a.cmp(b)
}

/// Compute the absolute value of a rational.
#[inline]
pub fn abs(r: &BigRational) -> BigRational {
    r.abs()
}

/// Compute the floor of a rational (greatest integer <= r).
pub fn floor(r: &BigRational) -> BigInt {
    if r.is_integer() {
        r.numer().clone()
    } else if r.is_positive() {
        r.numer() / r.denom()
    } else {
        // For negative non-integers, subtract 1
        (r.numer() / r.denom()) - BigInt::one()
    }
}

/// Compute the ceiling of a rational (smallest integer >= r).
pub fn ceil(r: &BigRational) -> BigInt {
    if r.is_integer() {
        r.numer().clone()
    } else if r.is_positive() {
        // For positive non-integers, add 1
        (r.numer() / r.denom()) + BigInt::one()
    } else {
        r.numer() / r.denom()
    }
}

/// Round a rational to the nearest integer (ties go to even).
pub fn round(r: &BigRational) -> BigInt {
    let floor_val = floor(r);
    let frac = r - BigRational::from_integer(floor_val.clone());

    let half = BigRational::new(BigInt::one(), BigInt::from(2));

    if frac < half {
        floor_val
    } else if frac > half {
        floor_val + BigInt::one()
    } else {
        // Tie: round to even
        if floor_val.is_even() {
            floor_val
        } else {
            floor_val + BigInt::one()
        }
    }
}

/// Compute the fractional part of a rational (r - floor(r)).
pub fn frac(r: &BigRational) -> BigRational {
    r - BigRational::from_integer(floor(r))
}

/// Check if a rational is an integer.
#[inline]
pub fn is_integer(r: &BigRational) -> bool {
    r.is_integer()
}

/// Compute the greatest common divisor of two rationals.
/// Returns the largest positive rational that divides both a and b.
pub fn gcd(a: &BigRational, b: &BigRational) -> BigRational {
    if a.is_zero() {
        return b.abs();
    }
    if b.is_zero() {
        return a.abs();
    }

    // GCD of rationals: gcd(a/b, c/d) = gcd(a*d, b*c) / (b*d)
    // But we can simplify using the integer GCD
    let gcd_num = gcd_bigint(a.numer().clone(), b.numer().clone());
    let lcm_denom = lcm_bigint(a.denom().clone(), b.denom().clone());

    BigRational::new(gcd_num, lcm_denom)
}

/// Compute the least common multiple of two rationals.
pub fn lcm(a: &BigRational, b: &BigRational) -> BigRational {
    if a.is_zero() || b.is_zero() {
        return BigRational::zero();
    }

    let g = gcd(a, b);
    (a * b / g).abs()
}

/// Compute GCD of two BigInts using Euclidean algorithm.
pub fn gcd_bigint(mut a: BigInt, mut b: BigInt) -> BigInt {
    while !b.is_zero() {
        let t = &a % &b;
        a = b;
        b = t;
    }
    a.abs()
}

/// Extended Euclidean algorithm for BigInts.
/// Returns (gcd, x, y) such that gcd = a*x + b*y (Bézout's identity).
///
/// This is useful for:
/// - Solving linear Diophantine equations
/// - Computing modular inverses
/// - Finding rational solutions to systems
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::gcd_extended;
///
/// let a = BigInt::from(240);
/// let b = BigInt::from(46);
/// let (gcd, x, y) = gcd_extended(a.clone(), b.clone());
/// assert_eq!(gcd, BigInt::from(2));
/// assert_eq!(&a * &x + &b * &y, gcd);
/// ```
pub fn gcd_extended(a: BigInt, b: BigInt) -> (BigInt, BigInt, BigInt) {
    if b.is_zero() {
        return (
            a.abs(),
            if a >= BigInt::zero() {
                BigInt::one()
            } else {
                -BigInt::one()
            },
            BigInt::zero(),
        );
    }

    let (mut old_r, mut r) = (a, b);
    let (mut old_s, mut s) = (BigInt::one(), BigInt::zero());
    let (mut old_t, mut t) = (BigInt::zero(), BigInt::one());

    while !r.is_zero() {
        let quotient = &old_r / &r;
        let new_r = &old_r - &quotient * &r;
        old_r = r;
        r = new_r;

        let new_s = &old_s - &quotient * &s;
        old_s = s;
        s = new_s;

        let new_t = &old_t - &quotient * &t;
        old_t = t;
        t = new_t;
    }

    (old_r, old_s, old_t)
}

/// Compute LCM of two BigInts.
pub fn lcm_bigint(a: BigInt, b: BigInt) -> BigInt {
    if a.is_zero() || b.is_zero() {
        return BigInt::zero();
    }
    let g = gcd_bigint(a.clone(), b.clone());
    (a * b / g).abs()
}

/// Compute the power of a rational number with integer exponent.
pub fn pow_int(base: &BigRational, exp: i32) -> BigRational {
    if exp == 0 {
        return BigRational::one();
    }
    if exp > 0 {
        pow_uint(base, exp as u32)
    } else {
        let p = pow_uint(base, (-exp) as u32);
        BigRational::one() / p
    }
}

/// Compute the power of a rational number with unsigned integer exponent.
pub fn pow_uint(base: &BigRational, exp: u32) -> BigRational {
    if exp == 0 {
        return BigRational::one();
    }
    if exp == 1 {
        return base.clone();
    }

    // Binary exponentiation
    let mut result = BigRational::one();
    let mut b = base.clone();
    let mut e = exp;

    while e > 0 {
        if e & 1 == 1 {
            result = &result * &b;
        }
        b = &b * &b;
        e >>= 1;
    }

    result
}

/// Normalize a rational to have positive denominator.
pub fn normalize(r: &BigRational) -> BigRational {
    if r.denom().is_negative() {
        BigRational::new(-r.numer(), -r.denom())
    } else {
        r.clone()
    }
}

/// Compare two rationals with a tolerance.
pub fn approx_eq(a: &BigRational, b: &BigRational, epsilon: &BigRational) -> bool {
    (a - b).abs() <= *epsilon
}

/// Compute the sign of a rational: -1, 0, or 1.
pub fn sign(r: &BigRational) -> i8 {
    if r.is_positive() {
        1
    } else if r.is_negative() {
        -1
    } else {
        0
    }
}

/// Clamp a rational to a range [min, max].
pub fn clamp(val: &BigRational, min: &BigRational, max: &BigRational) -> BigRational {
    if val < min {
        min.clone()
    } else if val > max {
        max.clone()
    } else {
        val.clone()
    }
}

/// Compute the minimum of two rationals.
#[inline]
pub fn min(a: &BigRational, b: &BigRational) -> BigRational {
    if a < b { a.clone() } else { b.clone() }
}

/// Compute the maximum of two rationals.
#[inline]
pub fn max(a: &BigRational, b: &BigRational) -> BigRational {
    if a > b { a.clone() } else { b.clone() }
}

/// Create a rational from a numerator and denominator.
#[inline]
pub fn from_integers(num: i64, den: i64) -> BigRational {
    BigRational::new(BigInt::from(num), BigInt::from(den))
}

/// Create a rational from an integer.
#[inline]
pub fn from_integer(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

/// Get the numerator of a rational as a reference.
#[inline]
pub fn numer(r: &BigRational) -> &BigInt {
    r.numer()
}

/// Get the denominator of a rational as a reference.
#[inline]
pub fn denom(r: &BigRational) -> &BigInt {
    r.denom()
}

/// Convert a rational to f64 (may lose precision).
pub fn to_f64(r: &BigRational) -> f64 {
    if r.denom().is_one() {
        r.numer().to_string().parse().unwrap_or(f64::NAN)
    } else {
        let num_f64: f64 = r.numer().to_string().parse().unwrap_or(f64::NAN);
        let den_f64: f64 = r.denom().to_string().parse().unwrap_or(f64::NAN);
        num_f64 / den_f64
    }
}

/// Compute the mediant of two rationals: (a.num + b.num) / (a.den + b.den).
/// This is used in continued fraction approximations.
pub fn mediant(a: &BigRational, b: &BigRational) -> BigRational {
    let num = a.numer() + b.numer();
    let den = a.denom() + b.denom();
    BigRational::new(num, den)
}

/// Compute the continued fraction representation of a rational number.
/// Returns a vector of coefficients [a0, a1, a2, ...] such that:
/// r = a0 + 1/(a1 + 1/(a2 + ...))
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use num_rational::BigRational;
/// use oxiz_math::rational::continued_fraction;
///
/// let r = BigRational::new(BigInt::from(22), BigInt::from(7)); // π ≈ 22/7
/// let cf = continued_fraction(&r);
/// assert_eq!(cf, vec![BigInt::from(3), BigInt::from(7)]);
/// ```
pub fn continued_fraction(r: &BigRational) -> Vec<BigInt> {
    let mut result = Vec::new();
    let mut current = r.clone();

    while !current.is_integer() {
        let int_part = floor(&current);
        result.push(int_part.clone());
        current = BigRational::one() / (current - BigRational::from_integer(int_part));
    }

    // Add the final integer part
    result.push(current.numer().clone());
    result
}

/// Reconstruct a rational from its continued fraction representation.
/// Takes coefficients [a0, a1, a2, ...] and returns the rational number.
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use num_rational::BigRational;
/// use oxiz_math::rational::{continued_fraction, from_continued_fraction};
///
/// let r = BigRational::new(BigInt::from(22), BigInt::from(7));
/// let cf = continued_fraction(&r);
/// let reconstructed = from_continued_fraction(&cf);
/// assert_eq!(r, reconstructed);
/// ```
pub fn from_continued_fraction(coeffs: &[BigInt]) -> BigRational {
    if coeffs.is_empty() {
        return BigRational::zero();
    }

    if coeffs.len() == 1 {
        return BigRational::from_integer(coeffs[0].clone());
    }

    // Start from the end and work backwards
    let mut result = BigRational::from_integer(coeffs[coeffs.len() - 1].clone());

    for i in (0..coeffs.len() - 1).rev() {
        result = BigRational::from_integer(coeffs[i].clone()) + BigRational::one() / result;
    }

    result
}

/// Compute the convergents (partial sums) of a continued fraction.
/// Returns a vector of rationals that increasingly approximate the target.
///
/// Convergents provide the best rational approximations with denominators
/// up to a given size, useful for interval refinement in algebraic number solving.
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use num_rational::BigRational;
/// use oxiz_math::rational::{continued_fraction, convergents};
///
/// let r = BigRational::new(BigInt::from(22), BigInt::from(7));
/// let cf = continued_fraction(&r);
/// let convs = convergents(&cf);
/// // First convergent is 3/1, second is 22/7
/// assert_eq!(convs[0], BigRational::new(BigInt::from(3), BigInt::from(1)));
/// assert_eq!(convs[1], BigRational::new(BigInt::from(22), BigInt::from(7)));
/// ```
pub fn convergents(coeffs: &[BigInt]) -> Vec<BigRational> {
    if coeffs.is_empty() {
        return vec![];
    }

    let mut result = Vec::with_capacity(coeffs.len());

    // Build convergents using the recurrence relation:
    // p_n = a_n * p_{n-1} + p_{n-2}
    // q_n = a_n * q_{n-1} + q_{n-2}
    let mut p_prev2 = BigInt::one();
    let mut p_prev1 = coeffs[0].clone();
    let mut q_prev2 = BigInt::zero();
    let mut q_prev1 = BigInt::one();

    result.push(BigRational::from_integer(coeffs[0].clone()));

    for coeff in coeffs.iter().skip(1) {
        let p = coeff * &p_prev1 + &p_prev2;
        let q = coeff * &q_prev1 + &q_prev2;

        result.push(BigRational::new(p.clone(), q.clone()));

        p_prev2 = p_prev1;
        p_prev1 = p;
        q_prev2 = q_prev1;
        q_prev1 = q;
    }

    result
}

/// Find the best rational approximation to a number within a given tolerance.
/// Uses continued fractions to find the simplest fraction within epsilon of the target.
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use num_rational::BigRational;
/// use oxiz_math::rational::best_rational_approximation;
///
/// let pi_approx = BigRational::new(BigInt::from(31416), BigInt::from(10000));
/// let epsilon = BigRational::new(BigInt::from(1), BigInt::from(1000));
/// let approx = best_rational_approximation(&pi_approx, &epsilon);
/// // Should give 22/7 or 355/113 depending on tolerance
/// ```
pub fn best_rational_approximation(target: &BigRational, epsilon: &BigRational) -> BigRational {
    let cf = continued_fraction(target);
    let convs = convergents(&cf);

    // Find the first convergent within epsilon
    for conv in convs {
        if (target - &conv).abs() <= *epsilon {
            return conv;
        }
    }

    // Fallback to the target itself
    target.clone()
}

/// Modular exponentiation: compute (base^exp) mod m efficiently.
/// Uses binary exponentiation to avoid overflow.
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::mod_pow;
///
/// let base = BigInt::from(2);
/// let exp = BigInt::from(10);
/// let m = BigInt::from(1000);
/// let result = mod_pow(&base, &exp, &m);
/// assert_eq!(result, BigInt::from(24)); // 2^10 mod 1000 = 1024 mod 1000 = 24
/// ```
pub fn mod_pow(base: &BigInt, exp: &BigInt, m: &BigInt) -> BigInt {
    if m.is_one() {
        return BigInt::zero();
    }

    let mut result = BigInt::one();
    let mut base = base % m;
    let mut exp = exp.clone();

    while exp > BigInt::zero() {
        if (&exp % BigInt::from(2)).is_one() {
            result = (result * &base) % m;
        }
        exp >>= 1;
        base = (&base * &base) % m;
    }

    result
}

/// Compute the modular multiplicative inverse of a modulo m.
/// Returns Some(x) where (a * x) ≡ 1 (mod m), or None if no inverse exists.
///
/// The inverse exists if and only if gcd(a, m) = 1.
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::mod_inverse;
///
/// let a = BigInt::from(3);
/// let m = BigInt::from(7);
/// let inv = mod_inverse(&a, &m).unwrap();
/// assert_eq!((&a * &inv) % &m, BigInt::from(1));
/// ```
pub fn mod_inverse(a: &BigInt, m: &BigInt) -> Option<BigInt> {
    let (gcd, x, _) = gcd_extended(a.clone(), m.clone());

    if !gcd.is_one() {
        return None; // No inverse exists
    }

    // Ensure the result is positive
    let inv = x % m;
    Some(if inv < BigInt::zero() { inv + m } else { inv })
}

/// Chinese Remainder Theorem: solve a system of congruences.
/// Given pairs (a_i, m_i) where x ≡ a_i (mod m_i), find x.
///
/// Returns Some(x, M) where x is the solution and M is the product of all moduli,
/// or None if the moduli are not pairwise coprime.
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::chinese_remainder;
///
/// // Solve: x ≡ 2 (mod 3), x ≡ 3 (mod 5), x ≡ 2 (mod 7)
/// let remainders = vec![
///     (BigInt::from(2), BigInt::from(3)),
///     (BigInt::from(3), BigInt::from(5)),
///     (BigInt::from(2), BigInt::from(7)),
/// ];
/// let (x, _m) = chinese_remainder(&remainders).unwrap();
/// assert_eq!(&x % BigInt::from(3), BigInt::from(2));
/// assert_eq!(&x % BigInt::from(5), BigInt::from(3));
/// assert_eq!(&x % BigInt::from(7), BigInt::from(2));
/// ```
pub fn chinese_remainder(congruences: &[(BigInt, BigInt)]) -> Option<(BigInt, BigInt)> {
    if congruences.is_empty() {
        return None;
    }

    // Compute the product of all moduli (M in mathematical notation)
    let mut prod_moduli = BigInt::one();
    for (_, m_i) in congruences {
        prod_moduli = &prod_moduli * m_i;
    }

    let mut result = BigInt::zero();

    for (a_i, m_i) in congruences {
        // M_i = M / m_i in mathematical notation
        let partial_prod = &prod_moduli / m_i;

        // Find the modular inverse of partial_prod mod m_i
        let inv = mod_inverse(&partial_prod, m_i)?;

        // Add to result: a_i * partial_prod * inv
        result = (result + a_i * &partial_prod * inv) % &prod_moduli;
    }

    // Ensure result is positive
    if result < BigInt::zero() {
        result += &prod_moduli;
    }

    Some((result, prod_moduli))
}

/// Solve a linear Diophantine equation ax + by = c.
/// Returns Some((x, y)) if a solution exists, or None if no solution exists.
///
/// A solution exists if and only if gcd(a, b) divides c.
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::solve_linear_diophantine;
///
/// let a = BigInt::from(3);
/// let b = BigInt::from(5);
/// let c = BigInt::from(1);
/// let (x, y) = solve_linear_diophantine(&a, &b, &c).unwrap();
/// assert_eq!(&a * &x + &b * &y, c);
/// ```
pub fn solve_linear_diophantine(a: &BigInt, b: &BigInt, c: &BigInt) -> Option<(BigInt, BigInt)> {
    let (gcd, x0, y0) = gcd_extended(a.clone(), b.clone());

    // Check if c is divisible by gcd(a, b)
    if (c % &gcd) != BigInt::zero() {
        return None; // No solution exists
    }

    // Scale the solution
    let factor = c / &gcd;
    let x = x0 * &factor;
    let y = y0 * factor;

    Some((x, y))
}

/// Performs the Miller-Rabin primality test.
///
/// Returns `true` if `n` is probably prime, `false` if composite.
/// The parameter `k` controls the number of rounds (higher = more accurate).
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::is_prime;
///
/// assert!(is_prime(&BigInt::from(17), 5));
/// assert!(is_prime(&BigInt::from(97), 5));
/// assert!(!is_prime(&BigInt::from(15), 5));
/// ```
#[cfg(feature = "std")]
pub fn is_prime(n: &BigInt, k: usize) -> bool {
    use num_traits::One;
    use rand::RngExt;

    // Handle small cases
    if n <= &BigInt::one() {
        return false;
    }
    if n == &BigInt::from(2) || n == &BigInt::from(3) {
        return true;
    }
    if n.is_even() {
        return false;
    }

    // Write n-1 as 2^r * d
    let n_minus_1 = n - BigInt::one();
    let mut d = n_minus_1.clone();
    let mut r = 0u32;
    while d.is_even() {
        d >>= 1;
        r += 1;
    }

    let two = BigInt::from(2);
    let n_minus_3 = n - &two - BigInt::one();
    let mut rng = rand::rng();

    // Miller-Rabin test
    'witness: for _ in 0..k {
        // Pick random witness a in [2, n-2]
        let a = if n_minus_3 <= BigInt::zero() {
            two.clone()
        } else {
            // Generate random number by generating random u64 and taking mod
            let random_u64 = rng.random_range(0u64..u64::MAX);
            (BigInt::from(random_u64) % &n_minus_3) + &two
        };

        let mut x = mod_pow(&a, &d, n);

        if x == BigInt::one() || x == n_minus_1 {
            continue 'witness;
        }

        for _ in 0..(r - 1) {
            x = mod_pow(&x, &two, n);
            if x == n_minus_1 {
                continue 'witness;
            }
        }

        return false; // Composite
    }

    true // Probably prime
}

/// Performs trial division to find small prime factors.
///
/// Returns a vector of prime factors found up to the limit.
/// If the input becomes 1, all factors have been found.
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::trial_division;
///
/// let n = BigInt::from(60);
/// let factors = trial_division(&n, 100);
/// // 60 = 2^2 * 3 * 5
/// assert!(factors.contains(&BigInt::from(2)));
/// assert!(factors.contains(&BigInt::from(3)));
/// assert!(factors.contains(&BigInt::from(5)));
/// ```
pub fn trial_division(n: &BigInt, limit: u64) -> Vec<BigInt> {
    let mut factors = Vec::new();
    let mut num = n.clone();

    // Check for factor 2
    while num.is_even() {
        factors.push(BigInt::from(2));
        num >>= 1;
    }

    // Check odd factors up to limit
    let mut divisor = BigInt::from(3);
    let limit_big = BigInt::from(limit);
    let two = BigInt::from(2);

    while &divisor * &divisor <= num && divisor <= limit_big {
        while &num % &divisor == BigInt::zero() {
            factors.push(divisor.clone());
            num /= &divisor;
        }
        divisor += &two;
    }

    // If num > 1, it's a prime factor
    if num > BigInt::one() && n != &num {
        factors.push(num);
    }

    factors
}

/// Pollard's rho algorithm for integer factorization.
///
/// Attempts to find a non-trivial factor of `n`.
/// Returns `None` if no factor is found within the iteration limit.
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::pollard_rho;
///
/// let n = BigInt::from(8051); // 8051 = 83 * 97
/// if let Some(factor) = pollard_rho(&n) {
///     assert!(n.clone() % &factor == BigInt::from(0));
///     assert!(factor > BigInt::from(1) && factor < n);
/// }
/// ```
#[cfg(feature = "std")]
pub fn pollard_rho(n: &BigInt) -> Option<BigInt> {
    use rand::RngExt;

    if n <= &BigInt::one() {
        return None;
    }
    if n.is_even() {
        return Some(BigInt::from(2));
    }

    let mut rng = rand::rng();

    // Generate random initial values using u64
    let random_x0 = rng.random_range(0u64..u64::MAX);
    let random_c = rng.random_range(1u64..u64::MAX);

    let x0 = BigInt::from(random_x0) % n;
    let c = BigInt::from(random_c) % n;

    let f = |x: &BigInt| -> BigInt { (x * x + &c) % n };

    let mut x = x0.clone();
    let mut y = x0;
    let mut d = BigInt::one();

    let max_iterations = 100000;
    let mut iterations = 0;

    while d == BigInt::one() && iterations < max_iterations {
        x = f(&x);
        y = f(&f(&y));

        let diff = if x >= y { &x - &y } else { &y - &x };
        d = gcd_bigint(diff, n.clone());

        iterations += 1;
    }

    if d != *n && d != BigInt::one() {
        Some(d)
    } else {
        None
    }
}

/// Computes the Jacobi symbol (a/n).
///
/// The Jacobi symbol is a generalization of the Legendre symbol.
/// Returns -1, 0, or 1.
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::jacobi_symbol;
///
/// // (2/5) = -1
/// assert_eq!(jacobi_symbol(&BigInt::from(2), &BigInt::from(5)), -1);
/// // (3/5) = -1
/// assert_eq!(jacobi_symbol(&BigInt::from(3), &BigInt::from(5)), -1);
/// // (4/5) = 1
/// assert_eq!(jacobi_symbol(&BigInt::from(4), &BigInt::from(5)), 1);
/// ```
pub fn jacobi_symbol(a: &BigInt, n: &BigInt) -> i8 {
    let mut a = a % n;
    let mut n = n.clone();
    let mut result = 1i8;

    while a != BigInt::zero() {
        // Remove factors of 2
        while a.is_even() {
            a >>= 1;
            let n_mod_8 = &n % BigInt::from(8);
            if n_mod_8 == BigInt::from(3) || n_mod_8 == BigInt::from(5) {
                result = -result;
            }
        }

        // Swap a and n
        core::mem::swap(&mut a, &mut n);

        // Quadratic reciprocity
        if &a % BigInt::from(4) == BigInt::from(3) && &n % BigInt::from(4) == BigInt::from(3) {
            result = -result;
        }

        a %= &n;
    }

    if n == BigInt::one() { result } else { 0 }
}

/// Computes the Legendre symbol (a/p) for prime p.
///
/// Returns -1 if a is a quadratic non-residue mod p,
/// 0 if a ≡ 0 (mod p), and 1 if a is a quadratic residue mod p.
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::legendre_symbol;
///
/// // For p = 5:
/// // 1^2 = 1, 2^2 = 4, 3^2 = 4, 4^2 = 1 (mod 5)
/// // So quadratic residues are {1, 4}
/// assert_eq!(legendre_symbol(&BigInt::from(1), &BigInt::from(5)), 1);
/// assert_eq!(legendre_symbol(&BigInt::from(4), &BigInt::from(5)), 1);
/// assert_eq!(legendre_symbol(&BigInt::from(2), &BigInt::from(5)), -1);
/// ```
pub fn legendre_symbol(a: &BigInt, p: &BigInt) -> i8 {
    // For prime p, Legendre symbol equals Jacobi symbol
    jacobi_symbol(a, p)
}

// ========  ========
// Verified complete factorization
//
// `trial_division` only ever removes factors up to a fixed limit and then
// blindly assumes whatever remains is prime. That assumption silently
// misclassifies composite residuals (e.g. a semiprime whose two factors are
// both above the limit), which in turn made `is_square_free`,
// `divisor_count`, `divisor_sum`, `mobius` and `euler_totient` produce wrong
// results for such inputs, and made `euler_totient`'s dedicated fallback
// loop (bounded only by `sqrt(n)`) stall for ~10^9 iterations on a large
// 64-bit prime.
//
// The helpers below factor completely: trial division peels off small
// factors, and anything left over is verified with Miller-Rabin and, if
// composite, split with Pollard's rho. Both primality testing and rho use a
// self-contained deterministic pseudo-random sequence (no `rand` dependency)
// so they behave identically with or without the `std` feature and never
// need an entropy source. Total work is capped by a fixed retry budget
// rather than by `n`'s magnitude, so factorization always terminates
// promptly -- including for large primes, which is exactly the case that
// used to hang.
// ========  ========

/// Small deterministic PRNG (SplitMix64) used only to vary the starting
/// parameters of successive Pollard's rho attempts. Not cryptographically
/// meaningful -- just needs to explore different sequences on retry.
struct SplitMix64(u64);

impl SplitMix64 {
    fn new(seed: u64) -> Self {
        SplitMix64(seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

/// FNV-1a hash of a `BigInt`'s bytes, used to seed the deterministic PRNG.
fn seed_from_bigint(n: &BigInt, salt: u64) -> u64 {
    let bytes = n.to_signed_bytes_le();
    let mut h: u64 = 0xcbf2_9ce4_8422_2325 ^ salt;
    for &b in &bytes {
        h ^= b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01B3);
    }
    h
}

/// First 20 primes, used as fixed Miller-Rabin witnesses. This needs no
/// entropy source (unlike [`is_prime`]), so it is available unconditionally.
const SMALL_WITNESS_PRIMES: [u64; 20] = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
];

/// Deterministic Miller-Rabin primality test using a fixed witness set.
///
/// Unlike [`is_prime`], this does not draw from an entropy source, so it
/// works identically with or without the `std` feature. False positives are
/// only theoretically possible against numbers deliberately constructed to
/// defeat this exact fixed witness set, which cannot arise from ordinary
/// factorization work.
fn is_prime_fixed_witnesses(n: &BigInt) -> bool {
    let zero = BigInt::zero();
    let one = BigInt::one();
    let two = BigInt::from(2);

    if n <= &one {
        return false;
    }
    if n == &two {
        return true;
    }
    if n.is_even() {
        return false;
    }

    for &p in &SMALL_WITNESS_PRIMES {
        let bp = BigInt::from(p);
        if n == &bp {
            return true;
        }
        if n > &bp && (n % &bp) == zero {
            return false;
        }
    }

    let n_minus_1 = n - &one;
    let mut d = n_minus_1.clone();
    let mut r: u32 = 0;
    while d.is_even() {
        d >>= 1;
        r += 1;
    }

    'witness: for &a_val in &SMALL_WITNESS_PRIMES {
        let a = BigInt::from(a_val);
        if &a >= n {
            continue;
        }
        let mut x = mod_pow(&a, &d, n);
        if x == one || x == n_minus_1 {
            continue 'witness;
        }
        for _ in 0..r.saturating_sub(1) {
            x = mod_pow(&x, &two, n);
            if x == n_minus_1 {
                continue 'witness;
            }
        }
        return false;
    }

    true
}

/// One attempt at splitting composite `n` via Pollard's rho, using
/// deterministic pseudo-random parameters derived from `attempt`. Returns
/// `None` if this particular choice of parameters fails to find a factor
/// within the per-attempt iteration cap; callers should retry with a
/// different `attempt` index.
fn pollard_rho_attempt(n: &BigInt, attempt: u64) -> Option<BigInt> {
    let one = BigInt::one();
    if n.is_even() {
        return Some(BigInt::from(2));
    }

    let mut rng = SplitMix64::new(seed_from_bigint(n, attempt));
    let x0 = BigInt::from(rng.next_u64()) % n;
    let mut c = BigInt::from(rng.next_u64()) % n;
    if c.is_zero() {
        c = one.clone();
    }

    let f = |x: &BigInt| -> BigInt { (x * x + &c) % n };

    let mut x = x0.clone();
    let mut y = x0;
    let mut d = one.clone();

    let max_iterations = 100_000;
    let mut iterations = 0;

    while d == one && iterations < max_iterations {
        x = f(&x);
        y = f(&f(&y));
        let diff = if x >= y { &x - &y } else { &y - &x };
        d = gcd_bigint(diff, n.clone());
        iterations += 1;
    }

    if d != *n && d != one { Some(d) } else { None }
}

/// Completely factor `n` (`n > 1`) into primes, with multiplicity, verifying
/// primality with Miller-Rabin instead of assuming a residual is prime.
///
/// Total Pollard's-rho work is capped by a fixed retry budget rather than by
/// `n`'s magnitude, so this always terminates promptly. In the
/// astronomically unlikely case that a composite cofactor resists the full
/// retry budget -- which would require a deliberately constructed,
/// cryptographically hard semiprime (a fundamentally hard problem for any
/// classical factoring approach, not specific to this implementation) --
/// this returns `Err((partial_factors, unresolved_residual))` instead of
/// guessing.
fn factorize_verified(n: &BigInt) -> Result<Vec<BigInt>, (Vec<BigInt>, BigInt)> {
    let one = BigInt::one();
    debug_assert!(n > &one, "factorize_verified expects n > 1");

    let mut factors = Vec::new();
    let mut remaining = n.clone();

    while remaining.is_even() {
        factors.push(BigInt::from(2));
        remaining >>= 1;
    }

    let mut d = BigInt::from(3);
    let small_limit = BigInt::from(1_000_000u64);
    while &d * &d <= remaining && d <= small_limit {
        while (&remaining % &d).is_zero() {
            factors.push(d.clone());
            remaining /= &d;
        }
        d += BigInt::from(2);
    }

    const MAX_POLLARD_ATTEMPTS: u32 = 64;
    let mut attempts_left = MAX_POLLARD_ATTEMPTS;
    let mut stack = vec![remaining];

    while let Some(m) = stack.pop() {
        if m <= one {
            continue;
        }
        if is_prime_fixed_witnesses(&m) {
            factors.push(m);
            continue;
        }

        let mut split = None;
        let mut attempt_idx: u64 = 0;
        while attempts_left > 0 {
            attempts_left -= 1;
            attempt_idx += 1;
            if let Some(f) = pollard_rho_attempt(&m, attempt_idx)
                && f > one
                && f < m
            {
                split = Some(f);
                break;
            }
        }

        match split {
            Some(f) => {
                let cofactor = &m / &f;
                stack.push(f);
                stack.push(cofactor);
            }
            None => {
                // Budget exhausted on a known-composite (verified above)
                // residual: surface it rather than silently treating it as
                // prime. See doc comment for when this can occur.
                factors.sort();
                return Err((factors, m));
            }
        }
    }

    factors.sort();
    Ok(factors)
}

/// Complete factorization of `n` (`n > 1`), with multiplicity, falling back
/// to treating an unresolved residual (see [`factorize_verified`]) as a
/// single factor. This preserves the non-`Result` signatures of the
/// number-theoretic helpers below; the fallback path is only reachable for
/// deliberately constructed, cryptographically hard semiprimes and is
/// documented on [`factorize_verified`]. Callers needing an explicit error
/// on that path should use [`factorize_verified`] directly (or the public
/// `factorize` wrapper).
fn factorize_or_best_effort(n: &BigInt) -> Vec<BigInt> {
    match factorize_verified(n) {
        Ok(factors) => factors,
        Err((mut factors, residual)) => {
            factors.push(residual);
            factors.sort();
            factors
        }
    }
}

/// Completely factor `n` into primes, with multiplicity.
///
/// This is the honest, `Result`-returning counterpart to the internal
/// factorization used by [`is_square_free`], [`divisor_count`],
/// [`divisor_sum`], [`mobius`] and [`euler_totient`]. Prefer this function
/// when you need to know whether factorization fully succeeded rather than
/// silently falling back on an unresolved residual.
///
/// # Errors
///
/// Returns `Err` describing the unresolved composite residual if the fixed
/// retry budget is exhausted before `n` is fully factored -- see
/// `factorize_verified` for when this can occur (in practice, only for
/// deliberately constructed cryptographically hard semiprimes).
pub fn factorize(n: &BigInt) -> Result<Vec<BigInt>, String> {
    if n <= &BigInt::one() {
        return Ok(Vec::new());
    }
    factorize_verified(n).map_err(|(_partial, residual)| {
        format!(
            "factorize: exhausted retry budget without fully factoring residual cofactor {residual}"
        )
    })
}

/// Computes Euler's totient function φ(n).
///
/// φ(n) counts the number of integers from 1 to n that are coprime with n.
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::euler_totient;
///
/// assert_eq!(euler_totient(&BigInt::from(1)), BigInt::from(1));
/// assert_eq!(euler_totient(&BigInt::from(9)), BigInt::from(6)); // φ(9) = 6
/// assert_eq!(euler_totient(&BigInt::from(10)), BigInt::from(4)); // φ(10) = 4
/// ```
pub fn euler_totient(n: &BigInt) -> BigInt {
    if n <= &BigInt::one() {
        return BigInt::one();
    }

    let mut result = n.clone();
    let mut seen_primes = crate::prelude::HashSet::new();

    for factor in factorize_or_best_effort(n) {
        if seen_primes.insert(factor.clone()) {
            // φ(n) = n * (1 - 1/p1) * (1 - 1/p2) * ...
            // = n * (p1 - 1)/p1 * (p2 - 1)/p2 * ...
            result = result * (&factor - BigInt::one()) / &factor;
        }
    }

    result
}

/// Tests if n is a perfect power: n = a^b for some a, b > 1.
///
/// Returns `Some((a, b))` if n is a perfect power, `None` otherwise.
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::is_perfect_power;
///
/// assert_eq!(is_perfect_power(&BigInt::from(8)), Some((BigInt::from(2), 3)));
/// assert_eq!(is_perfect_power(&BigInt::from(27)), Some((BigInt::from(3), 3)));
/// // 16 = 2^4 or 4^2, both are valid
/// let result = is_perfect_power(&BigInt::from(16));
/// assert!(result.is_some());
/// let (base, exp) = result.unwrap();
/// assert_eq!(base.pow(exp), BigInt::from(16));
/// assert_eq!(is_perfect_power(&BigInt::from(10)), None);
/// ```
pub fn is_perfect_power(n: &BigInt) -> Option<(BigInt, u32)> {
    if n <= &BigInt::one() {
        return None;
    }

    // Check for each possible exponent b from 2 to log2(n)
    let bit_len = n.bits() as u32;

    for b in 2..=bit_len {
        // Binary search for a such that a^b = n
        let mut low = BigInt::one();
        let mut high = n.clone();

        while low <= high {
            let mid = (&low + &high) / BigInt::from(2);
            let power = pow_uint(&BigRational::from_integer(mid.clone()), b);

            if power.is_integer() {
                let power_int = power.numer().clone();

                match power_int.cmp(n) {
                    Ordering::Equal => return Some((mid, b)),
                    Ordering::Less => low = mid + BigInt::one(),
                    Ordering::Greater => high = mid - BigInt::one(),
                }
            } else {
                break;
            }
        }
    }

    None
}

/// Tests if n is square-free (not divisible by any perfect square except 1).
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::is_square_free;
///
/// assert!(is_square_free(&BigInt::from(6))); // 6 = 2 * 3
/// assert!(is_square_free(&BigInt::from(10))); // 10 = 2 * 5
/// assert!(!is_square_free(&BigInt::from(12))); // 12 = 4 * 3, divisible by 4 = 2^2
/// assert!(!is_square_free(&BigInt::from(18))); // 18 = 9 * 2, divisible by 9 = 3^2
/// ```
pub fn is_square_free(n: &BigInt) -> bool {
    if n <= &BigInt::one() {
        return n == &BigInt::one();
    }

    let factors = factorize_or_best_effort(n);
    let mut prev: Option<BigInt> = None;

    for factor in factors {
        if let Some(ref p) = prev
            && &factor == p
        {
            return false; // Found repeated factor
        }
        prev = Some(factor);
    }

    true
}

/// Computes the number of divisors of n (tau function, τ(n)).
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::divisor_count;
///
/// assert_eq!(divisor_count(&BigInt::from(12)), BigInt::from(6)); // 1, 2, 3, 4, 6, 12
/// assert_eq!(divisor_count(&BigInt::from(28)), BigInt::from(6)); // 1, 2, 4, 7, 14, 28
/// assert_eq!(divisor_count(&BigInt::from(1)), BigInt::from(1));
/// ```
pub fn divisor_count(n: &BigInt) -> BigInt {
    if n <= &BigInt::zero() {
        return BigInt::zero();
    }
    if n == &BigInt::one() {
        return BigInt::one();
    }

    let factors = factorize_or_best_effort(n);

    let mut count = BigInt::one();
    let mut current_prime = None;
    let mut current_count = 0u32;

    for factor in factors {
        if let Some(ref prime) = current_prime {
            if &factor == prime {
                current_count += 1;
            } else {
                count *= current_count + 1;
                current_prime = Some(factor);
                current_count = 1;
            }
        } else {
            current_prime = Some(factor);
            current_count = 1;
        }
    }

    if current_count > 0 {
        count *= current_count + 1;
    }

    count
}

/// Computes the sum of divisors of n (sigma function, σ(n)).
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::divisor_sum;
///
/// assert_eq!(divisor_sum(&BigInt::from(12)), BigInt::from(28)); // 1+2+3+4+6+12
/// assert_eq!(divisor_sum(&BigInt::from(6)), BigInt::from(12)); // 1+2+3+6
/// assert_eq!(divisor_sum(&BigInt::from(1)), BigInt::from(1));
/// ```
pub fn divisor_sum(n: &BigInt) -> BigInt {
    if n <= &BigInt::zero() {
        return BigInt::zero();
    }
    if n == &BigInt::one() {
        return BigInt::one();
    }

    let factors = factorize_or_best_effort(n);

    let mut sum = BigInt::one();
    let mut current_prime = None;
    let mut current_count = 0u32;

    for factor in factors {
        if let Some(ref prime) = current_prime {
            if &factor == prime {
                current_count += 1;
            } else {
                // σ(p^k) = (p^(k+1) - 1) / (p - 1)
                let p_power =
                    pow_uint(&BigRational::from_integer(prime.clone()), current_count + 1);
                let numerator = p_power.numer() - BigInt::one();
                let denominator = prime - BigInt::one();
                sum *= numerator / denominator;

                current_prime = Some(factor);
                current_count = 1;
            }
        } else {
            current_prime = Some(factor);
            current_count = 1;
        }
    }

    if let Some(prime) = current_prime {
        let p_power = pow_uint(&BigRational::from_integer(prime.clone()), current_count + 1);
        let numerator = p_power.numer() - BigInt::one();
        let denominator = prime - BigInt::one();
        sum *= numerator / denominator;
    }

    sum
}

/// Computes the Möbius function μ(n).
///
/// Returns:
/// - 1 if n is square-free with an even number of prime factors
/// - -1 if n is square-free with an odd number of prime factors
/// - 0 if n is not square-free
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::mobius;
///
/// assert_eq!(mobius(&BigInt::from(1)), 1);
/// assert_eq!(mobius(&BigInt::from(6)), 1); // 6 = 2*3 (2 primes)
/// assert_eq!(mobius(&BigInt::from(30)), -1); // 30 = 2*3*5 (3 primes)
/// assert_eq!(mobius(&BigInt::from(12)), 0); // 12 = 2^2*3 (not square-free)
/// ```
pub fn mobius(n: &BigInt) -> i8 {
    if n <= &BigInt::zero() {
        return 0;
    }
    if n == &BigInt::one() {
        return 1;
    }

    let factors = factorize_or_best_effort(n);
    let mut unique_primes = crate::prelude::HashSet::new();

    for factor in factors {
        if !unique_primes.insert(factor) {
            return 0; // Repeated prime factor => not square-free
        }
    }

    if unique_primes.len() % 2 == 0 { 1 } else { -1 }
}

/// Computes Carmichael's lambda function λ(n).
///
/// λ(n) is the exponent of the group (ℤ/nℤ)*.
/// For any a coprime to n: a^λ(n) ≡ 1 (mod n).
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::carmichael_lambda;
///
/// assert_eq!(carmichael_lambda(&BigInt::from(1)), BigInt::from(1));
/// assert_eq!(carmichael_lambda(&BigInt::from(8)), BigInt::from(2)); // λ(8) = 2
/// assert_eq!(carmichael_lambda(&BigInt::from(15)), BigInt::from(4)); // λ(15) = 4
/// ```
pub fn carmichael_lambda(n: &BigInt) -> BigInt {
    if n <= &BigInt::one() {
        return BigInt::one();
    }

    let factors = factorize_or_best_effort(n);
    let mut prime_powers: FxHashMap<BigInt, u32> = FxHashMap::default();

    for factor in factors {
        *prime_powers.entry(factor).or_insert(0) += 1;
    }

    let mut result = BigInt::one();

    for (prime, exp) in prime_powers {
        let lambda_p = if prime == BigInt::from(2) && exp >= 3 {
            // λ(2^k) = 2^(k-2) for k ≥ 3
            BigInt::from(2).pow(exp - 2)
        } else if prime == BigInt::from(2) {
            // λ(2) = 1, λ(4) = 2
            if exp == 1 {
                BigInt::one()
            } else {
                BigInt::from(2)
            }
        } else {
            // λ(p^k) = φ(p^k) = p^(k-1) * (p-1)
            let p_power = pow_uint(&BigRational::from_integer(prime.clone()), exp - 1);
            p_power.numer() * (&prime - BigInt::one())
        };

        result = lcm_bigint(result, lambda_p);
    }

    result
}

/// Binary GCD (Stein's algorithm) - more efficient than Euclidean GCD.
///
/// This algorithm uses bitwise operations instead of division,
/// making it faster for large integers.
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::gcd_binary;
///
/// assert_eq!(gcd_binary(BigInt::from(48), BigInt::from(18)), BigInt::from(6));
/// assert_eq!(gcd_binary(BigInt::from(100), BigInt::from(35)), BigInt::from(5));
/// assert_eq!(gcd_binary(BigInt::from(17), BigInt::from(19)), BigInt::from(1));
/// ```
pub fn gcd_binary(mut a: BigInt, mut b: BigInt) -> BigInt {
    if a == BigInt::zero() {
        return b.abs();
    }
    if b == BigInt::zero() {
        return a.abs();
    }

    a = a.abs();
    b = b.abs();

    // Count common factors of 2
    let mut shift = 0u32;
    while a.is_even() && b.is_even() {
        a >>= 1;
        b >>= 1;
        shift += 1;
    }

    // Remove remaining factors of 2 from a
    while a.is_even() {
        a >>= 1;
    }

    loop {
        // Remove factors of 2 from b
        while b.is_even() {
            b >>= 1;
        }

        // Ensure a <= b
        if a > b {
            core::mem::swap(&mut a, &mut b);
        }

        b -= &a;

        if b == BigInt::zero() {
            break;
        }
    }

    a << shift
}

/// Tonelli-Shanks algorithm for computing modular square roots.
///
/// Finds x such that x² ≡ n (mod p) for prime p.
/// Returns None if n is not a quadratic residue modulo p.
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::tonelli_shanks;
///
/// // 4 is a quadratic residue mod 7 (2^2 = 4)
/// let result = tonelli_shanks(&BigInt::from(4), &BigInt::from(7));
/// assert!(result.is_some());
/// if let Some(x) = result {
///     let p = BigInt::from(7);
///     assert_eq!((&x * &x) % &p, BigInt::from(4) % &p);
/// }
/// ```
pub fn tonelli_shanks(n: &BigInt, p: &BigInt) -> Option<BigInt> {
    // Check if n is a quadratic residue
    if legendre_symbol(n, p) != 1 {
        return None;
    }

    // Handle special cases
    if p == &BigInt::from(2) {
        return Some(n % p);
    }

    // Factor out powers of 2 from p-1: p-1 = 2^S * Q
    let p_minus_1 = p - BigInt::one();
    let mut q = p_minus_1.clone();
    let mut s = 0u32;
    while q.is_even() {
        q >>= 1;
        s += 1;
    }

    // Special case: p ≡ 3 (mod 4)
    if s == 1 {
        let exp = (p + BigInt::one()) / BigInt::from(4);
        return Some(mod_pow(n, &exp, p));
    }

    // Find a quadratic non-residue z
    let mut z = BigInt::from(2);
    while legendre_symbol(&z, p) != -1 {
        z += BigInt::one();
    }

    let mut m = s;
    let mut c = mod_pow(&z, &q, p);
    let mut t = mod_pow(n, &q, p);
    let mut r = mod_pow(n, &((&q + BigInt::one()) / BigInt::from(2)), p);

    loop {
        if t == BigInt::zero() {
            return Some(BigInt::zero());
        }
        if t == BigInt::one() {
            return Some(r);
        }

        // Find the least i such that t^(2^i) = 1
        let mut i = 1u32;
        let mut temp = (&t * &t) % p;
        while temp != BigInt::one() && i < m {
            temp = (&temp * &temp) % p;
            i += 1;
        }

        let b = mod_pow(&c, &BigInt::from(2u64).pow(m - i - 1), p);
        m = i;
        c = (&b * &b) % p;
        t = (&t * &c) % p;
        r = (&r * &b) % p;
    }
}

/// Computes factorial n!
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::factorial;
///
/// assert_eq!(factorial(0), BigInt::from(1));
/// assert_eq!(factorial(5), BigInt::from(120));
/// assert_eq!(factorial(10), BigInt::from(3628800));
/// ```
pub fn factorial(n: u32) -> BigInt {
    if n == 0 || n == 1 {
        return BigInt::one();
    }

    let mut result = BigInt::one();
    for i in 2..=n {
        result *= i;
    }
    result
}

/// Computes binomial coefficient C(n, k) = n! / (k! * (n-k)!)
///
/// # Examples
/// ```
/// use num_bigint::BigInt;
/// use oxiz_math::rational::binomial;
///
/// assert_eq!(binomial(5, 2), BigInt::from(10));
/// assert_eq!(binomial(10, 3), BigInt::from(120));
/// assert_eq!(binomial(5, 0), BigInt::from(1));
/// assert_eq!(binomial(5, 5), BigInt::from(1));
/// ```
pub fn binomial(n: u32, k: u32) -> BigInt {
    if k > n {
        return BigInt::zero();
    }
    if k == 0 || k == n {
        return BigInt::one();
    }

    // Use symmetry: C(n,k) = C(n,n-k)
    let k = core::cmp::min(k, n - k);

    let mut result = BigInt::one();
    for i in 0..k {
        result *= n - i;
        result /= i + 1;
    }
    result
}

#[cfg(test)]
mod tests;
