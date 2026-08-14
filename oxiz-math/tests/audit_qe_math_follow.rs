//! Regression tests for the `qe-math-follow` package (wave-1 follow-up):
//!
//! 1. `oxiz_math::rational::carmichael_lambda` used `trial_division` with a
//!    fixed limit and silently treated any un-factored residual as prime,
//!    just like the other number-theory helpers fixed in wave 1
//!    (`is_square_free`, `divisor_count`, `divisor_sum`, `mobius`,
//!    `euler_totient`). It now routes through the same verified,
//!    complete-or-explicit-error factorization used by those helpers.
//! 2. `oxiz_math::grobner::buchberger::NraSolver::check_sat` used to report
//!    `Unknown` for *every* non-constant inequality, even purely linear
//!    ones. It now decides linear (affine) systems -- including a mix of
//!    strict/non-strict inequalities and `!=` disequalities -- exactly via
//!    Fourier-Motzkin elimination, only falling back to `Unknown` when a
//!    genuinely non-linear constraint remains (or a search budget is
//!    exhausted).
//!
//! These exercise the *public* API only; unit-level regressions for
//! internals (e.g. the Fourier-Motzkin resolvent construction) live in the
//! `#[cfg(test)]` module inside `oxiz-math/src/grobner/buchberger.rs`
//! itself.
//!
//! A third finding in this package's scope --
//! `oxiz-core/src/qe/array/mod.rs` no longer re-exporting the disabled
//! placeholder `quantifier_elim` types -- is a pure API-surface change in a
//! different crate (`oxiz-core`) with no runtime behavior to regression-test
//! from here; it is covered by `cargo check -p oxiz-core` producing zero
//! warnings (no more dead/unused placeholder re-export) and by
//! `oxiz-core/src/qe/array/quantifier_elim.rs`'s own existing tests.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};
use oxiz_math::grobner::buchberger::{PolynomialConstraint, Relation};
use oxiz_math::grobner::{NraSolver, SatResult};
use oxiz_math::polynomial::Polynomial;
use oxiz_math::rational::{carmichael_lambda, euler_totient, is_prime};

/// Find the first prime strictly greater than `start` using the crate's own
/// Miller-Rabin test, so the test doesn't depend on a hand-verified magic
/// constant (mirrors the helper in `audit_math_misc.rs`).
fn next_prime_after(start: u64) -> BigInt {
    let mut candidate = BigInt::from(start) + BigInt::one();
    loop {
        if is_prime(&candidate, 30) {
            return candidate;
        }
        candidate += BigInt::one();
    }
}

fn rat(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

// ========  ========
// Finding 1: carmichael_lambda beyond the old trial_division limit.
// ========  ========

#[test]
fn carmichael_lambda_correct_for_large_prime_beyond_trial_division_limit() {
    // Regression: carmichael_lambda(p) used trial_division(n, 1_000_000),
    // which for a prime p > 1_000_000 returns an *empty* factor list (no
    // factor <= 1_000_000 divides p), leaving `prime_powers` empty and thus
    // returning lcm() over zero terms = 1, instead of the correct
    // lambda(p) = p - 1 for prime p.
    let p = next_prime_after(1_000_000);
    let expected = &p - BigInt::one();
    assert_eq!(
        carmichael_lambda(&p),
        expected,
        "lambda(p) = p - 1 for prime p, even when p exceeds the old trial-division limit"
    );
}

#[test]
fn carmichael_lambda_correct_for_semiprime_with_both_factors_above_limit() {
    // lambda(p*q) = lcm(p-1, q-1) for distinct odd primes p, q.
    let p = next_prime_after(1_000_000);
    let q = next_prime_after(2_000_000);
    assert_ne!(p, q);
    let n = &p * &q;

    let lambda_p = &p - BigInt::one();
    let lambda_q = &q - BigInt::one();
    let expected = num_integer::Integer::lcm(&lambda_p, &lambda_q);

    assert_eq!(carmichael_lambda(&n), expected);
}

#[test]
fn carmichael_lambda_matches_euler_totient_for_prime_power_of_odd_prime() {
    // For an odd prime p, lambda(p^k) = phi(p^k) (they only diverge at
    // powers of 2 >= 8). Cross-check against the (already-fixed in wave 1)
    // euler_totient for a prime beyond the old limit.
    let p = next_prime_after(1_000_000);
    let n = &p * &p; // p^2
    assert_eq!(carmichael_lambda(&n), euler_totient(&n));
}

#[test]
fn carmichael_lambda_small_values_still_correct() {
    // No-regression check against the documented examples.
    assert_eq!(carmichael_lambda(&BigInt::from(1)), BigInt::from(1));
    assert_eq!(carmichael_lambda(&BigInt::from(8)), BigInt::from(2));
    assert_eq!(carmichael_lambda(&BigInt::from(15)), BigInt::from(4));
    assert_eq!(carmichael_lambda(&BigInt::zero()), BigInt::one());
}

// ========  ========
// Finding 2: NraSolver::check_sat now decides linear inequality systems.
// ========  ========

#[test]
fn nra_solver_decides_classic_strict_contradiction() {
    // The textbook motivating example from check_sat's own doc comment:
    // "asserting x > 0 and x < 0 ... is unsatisfiable" must now actually be
    // decided as Unsat, not reported Unknown.
    let mut solver = NraSolver::new();
    let x = Polynomial::from_var(0);
    solver.add_constraint(PolynomialConstraint::greater(x.clone()));
    solver.add_constraint(PolynomialConstraint::less(x));

    assert_eq!(solver.check_sat(), SatResult::Unsat);
}

#[test]
fn nra_solver_decides_satisfiable_linear_system_via_equality_reduction() {
    // x = 5 (equality), then x > 3: reduces to the constant 5 > 3, so this
    // was already decided before this fix. Combine it with an *additional*
    // genuinely non-constant linear inequality on a second variable to
    // confirm the new decision procedure and the pre-existing constant path
    // compose correctly.
    let mut solver = NraSolver::new();
    let x = Polynomial::from_var(0);
    let x_minus_5 = Polynomial::from_coeffs_int(&[(1, &[(0, 1)]), (-5, &[])]);
    solver.add_equality(x_minus_5);
    solver.add_constraint(PolynomialConstraint::greater(
        x.clone() - Polynomial::constant(rat(3)),
    ));

    // y < 0 with y >= -1 (a fresh, still-linear, still-undecided-until-now
    // constraint on a second variable): satisfiable, e.g. y = -0.5.
    let y = Polynomial::from_var(1);
    solver.add_constraint(PolynomialConstraint::less(y.clone()));
    solver.add_constraint(PolynomialConstraint::greater_equal(
        y + Polynomial::constant(rat(1)),
    ));

    assert_eq!(solver.check_sat(), SatResult::Sat);
}

#[test]
fn nra_solver_disequality_with_equality_pin_is_unsat() {
    // x = 0 (equality) combined with x != 0: the equality Gröbner
    // reduction already turns "x != 0" into the constant "0 != 0", which
    // is decided false without ever reaching the linear-inequality
    // decision procedure. Documented here as a boundary regression check
    // between the equality path and the new inequality path.
    let mut solver = NraSolver::new();
    let x = Polynomial::from_var(0);
    solver.add_equality(x.clone());
    solver.add_constraint(PolynomialConstraint::not_equal(x));

    assert_eq!(solver.check_sat(), SatResult::Unsat);
}

#[test]
fn nra_solver_relation_variants_all_route_through_linear_decision() {
    // Sanity sweep over every `Relation` variant on a genuinely
    // non-constant linear polynomial, checked against hand-verified
    // expected results.
    let cases: &[(Relation, bool)] = &[
        (Relation::Greater, true),      // x - 1 > 0 has a solution (x=2)
        (Relation::GreaterEqual, true), // x - 1 >= 0 has a solution (x=1)
        (Relation::Less, true),         // x - 1 < 0 has a solution (x=0)
        (Relation::LessEqual, true),    // x - 1 <= 0 has a solution (x=1)
        (Relation::NotEqual, true),     // x - 1 != 0 has a solution (x=0)
    ];

    for &(relation, expect_sat) in cases {
        let mut solver = NraSolver::new();
        let x_minus_1 = Polynomial::from_coeffs_int(&[(1, &[(0, 1)]), (-1, &[])]);
        solver.add_constraint(PolynomialConstraint::new(x_minus_1, relation));
        let result = solver.check_sat();
        let is_sat = result == SatResult::Sat;
        assert_eq!(
            is_sat, expect_sat,
            "relation {relation:?} expected sat={expect_sat} but got {result:?}"
        );
    }
}
