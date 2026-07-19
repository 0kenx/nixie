//! Regression tests for audited defects in the `math-misc` package
//! (`oxiz-math/src/simplex.rs`, `oxiz-math/src/fast_rational.rs`,
//! `oxiz-math/src/rational/mod.rs`).
//!
//! These exercise the *public* API only; unit-level regressions for
//! internals live in `#[cfg(test)]` modules within the owned source files
//! themselves.

use num_bigint::BigInt;
use num_traits::One;
use oxiz_math::fast_rational::FastRational;
use oxiz_math::rational::{
    divisor_count, divisor_sum, euler_totient, factorize, is_prime, is_square_free, mobius,
};
use oxiz_math::simplex::{BoundType, Row, SimplexResult, SimplexTableau};

/// Find the first prime strictly greater than `start` using the crate's own
/// Miller-Rabin test, so the test doesn't depend on a hand-verified magic
/// constant.
fn next_prime_after(start: u64) -> BigInt {
    let mut candidate = BigInt::from(start) + BigInt::one();
    loop {
        if is_prime(&candidate, 30) {
            return candidate;
        }
        candidate += BigInt::one();
    }
}

// ---------------------------------------------------------------------------
// rational/mod.rs: number-theory helpers must be correct beyond the old
// trial-division limit (100_000 / 1_000_000), and must never hang.
// ---------------------------------------------------------------------------

#[test]
fn is_square_free_false_for_square_of_prime_beyond_trial_division_limit() {
    // Regression: is_square_free(p^2) used to return `true` for any prime
    // p > 100_000 because trial_division silently dropped the un-factored
    // residual instead of reporting it as a repeated factor.
    let p = next_prime_after(100_000);
    let n = &p * &p;
    assert!(
        !is_square_free(&n),
        "p^2 for prime p={p} beyond the old trial-division limit must not be square-free"
    );
}

#[test]
fn is_square_free_true_for_product_of_two_distinct_large_primes() {
    let p = next_prime_after(100_000);
    let q = next_prime_after(200_000);
    let n = &p * &q;
    assert!(is_square_free(&n));
}

#[test]
fn divisor_count_sum_mobius_correct_for_semiprime_with_both_factors_above_limit() {
    // Regression: divisor_count/divisor_sum/mobius used to mis-handle a
    // semiprime whose *both* factors exceed the trial-division limit,
    // because the un-factored residual was blindly treated as a single
    // prime factor (correct here only by luck) or dropped/mis-grouped.
    let p = next_prime_after(1_000_000);
    let q = next_prime_after(2_000_000);
    assert_ne!(p, q);
    let n = &p * &q;

    // tau(p*q) = 4 for distinct primes p, q.
    assert_eq!(divisor_count(&n), BigInt::from(4));

    // sigma(p*q) = 1 + p + q + p*q for distinct primes p, q.
    let expected_sum = BigInt::one() + &p + &q + &n;
    assert_eq!(divisor_sum(&n), expected_sum);

    // mu(p*q) = 1 (square-free, even number of prime factors: 2).
    assert_eq!(mobius(&n), 1);
}

#[test]
fn mobius_zero_for_square_of_large_prime() {
    let p = next_prime_after(500_000);
    let n = &p * &p;
    assert_eq!(mobius(&n), 0);
}

#[test]
fn euler_totient_terminates_and_is_correct_for_a_large_prime() {
    // Regression: euler_totient's second loop trial-divided a BigInt
    // divisor up to sqrt(n) with no bound, so a large prime input could
    // stall for ~10^9 iterations. This must now return promptly.
    //
    // Use a prime comfortably beyond any trial-division limit that was
    // previously hard-coded (1_000_000) so the old code path (had it not
    // hung) would have needed to fall through to the unbounded loop.
    let p = next_prime_after(50_000_000);
    let phi = euler_totient(&p);
    assert_eq!(phi, &p - BigInt::one());
}

#[test]
fn euler_totient_correct_for_semiprime_beyond_limit() {
    let p = next_prime_after(100_000);
    let q = next_prime_after(300_000);
    let n = &p * &q;
    // phi(p*q) = (p-1)*(q-1) for distinct primes p, q.
    let expected = (&p - BigInt::one()) * (&q - BigInt::one());
    assert_eq!(euler_totient(&n), expected);
}

#[test]
fn factorize_public_api_reconstructs_n_and_reports_errors_honestly() {
    let p = next_prime_after(10_000);
    let q = next_prime_after(20_000);
    let n = &p * &p * &q;

    let factors = factorize(&n).expect("factorize should succeed for an ordinary semiprime-ish n");
    let product: BigInt = factors.iter().product();
    assert_eq!(product, n);
    assert_eq!(factors.len(), 3);

    // n <= 1 has no prime factors.
    assert_eq!(
        factorize(&BigInt::one()).expect("1 factors to the empty list"),
        Vec::<BigInt>::new()
    );
}

// ---------------------------------------------------------------------------
// fast_rational.rs: i64::MIN must never be silently corrupted by
// saturating_abs before reaching gcd_i64.
// ---------------------------------------------------------------------------

#[test]
fn fast_rational_mul_i64_min_matches_bigint_arithmetic() {
    let a = FastRational::from(i64::MIN);
    let b = FastRational::from((1i64, 7i64));
    let result = a * b;

    let expected = num_rational::BigRational::new(BigInt::from(i64::MIN), BigInt::from(7));
    assert_eq!(result.to_big_rational(), expected);
}

// ---------------------------------------------------------------------------
// simplex.rs: a non-basic variable violating its own (newly tightened)
// bound must be repaired, not silently ignored by check().
// ---------------------------------------------------------------------------

#[test]
fn simplex_detects_infeasibility_from_non_basic_bound_violation() {
    let mut tableau = SimplexTableau::new();

    let x = tableau.fresh_var();
    let y = tableau.fresh_var();

    // y = x
    let mut row = Row::new(y);
    row.coeffs.insert(x, num_bigint::BigInt::one().into());
    tableau.add_row(row).expect("row should be added");

    tableau
        .add_bound(x, BoundType::Lower, num_bigint::BigInt::from(5).into(), 0)
        .expect("x >= 5 is not itself a conflict");

    let add_upper = tableau.add_bound(y, BoundType::Upper, num_bigint::BigInt::from(3).into(), 1);

    let is_unsat = match add_upper {
        Err(_) => true,
        Ok(()) => tableau.check().is_err(),
    };

    assert!(
        is_unsat,
        "system (y = x, x >= 5, y <= 3) is infeasible and must never be reported Sat"
    );

    // Also confirm the positive control still works: check() returning Ok
    // must actually mean Sat for a genuinely feasible tightened system.
    let mut tableau2 = SimplexTableau::new();
    let x2 = tableau2.fresh_var();
    let y2 = tableau2.fresh_var();
    let mut row2 = Row::new(y2);
    row2.coeffs.insert(x2, num_bigint::BigInt::one().into());
    tableau2.add_row(row2).expect("row should be added");
    tableau2
        .add_bound(
            y2,
            BoundType::Upper,
            num_bigint::BigInt::from(100).into(),
            0,
        )
        .expect("test operation should succeed");
    tableau2
        .add_bound(x2, BoundType::Lower, num_bigint::BigInt::from(5).into(), 1)
        .expect("test operation should succeed");
    assert_eq!(
        tableau2.check().expect("should be feasible"),
        SimplexResult::Sat
    );
    assert!(tableau2.is_feasible());
}
