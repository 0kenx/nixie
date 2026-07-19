//! Regression tests for audited soundness defects in the `math-poly` package.
//!
//! Covers three findings:
//! 1. Sturm sequence built from pseudo-remainders without sign normalization
//!    produced wrong real-root counts for polynomials with negative leading
//!    coefficients (extended_ops.rs).
//! 2. `NraSolver::check_sat` returned `Sat` while ignoring non-constant linear
//!    inequalities such as `{x > 0, x < 0}` (buchberger.rs). This has since
//!    been superseded by a real decision procedure: non-constant *linear*
//!    inequalities left over after Gröbner reduction are now routed through
//!    an exact-rational Fourier-Motzkin elimination
//!    (`grobner::linear_arith::decide_linear_arms`), so systems like
//!    `{x > 0, x < 0}` are genuinely decided `Unsat` and `{x > 0}` alone is
//!    genuinely decided `Sat`, rather than reported `Unknown`. The tests
//!    below assert those correct verdicts (only a truly non-linear leftover,
//!    e.g. `x^2 > 0`, still falls back to the honest `Unknown`).
//! 3. `reduce()` silently dropped the unreduced tail when the 1000-iteration
//!    cap was hit, returning a polynomial not equivalent to the input modulo
//!    the ideal (buchberger.rs).

use num_bigint::BigInt;
use num_rational::BigRational;
use oxiz_math::grobner::buchberger::PolynomialConstraint;
use oxiz_math::grobner::{NraSolver, SatResult, reduce};
use oxiz_math::polynomial::Polynomial;

fn rat(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

/// Finding 1: `-x^2 + 1` has exactly two real roots (-1 and 1), both inside
/// (-2, 2). The unsigned pseudo-remainder Sturm chain reported 0.
#[test]
fn sturm_count_roots_negative_leading_coeff() {
    // p = -x^2 + 1
    let p = Polynomial::from_coeffs_int(&[(-1, &[(0, 2)]), (1, &[])]);
    let count = p.count_roots_in_interval(0, &rat(-2), &rat(2));
    assert_eq!(count, 2, "-x^2+1 must have 2 real roots in (-2,2)");
}

/// Sanity: positive-leading counterpart must also count 2 roots, and the two
/// polynomials must agree (they have the same roots).
#[test]
fn sturm_count_roots_sign_agnostic() {
    let p_neg = Polynomial::from_coeffs_int(&[(-1, &[(0, 2)]), (1, &[])]);
    let p_pos = Polynomial::from_coeffs_int(&[(1, &[(0, 2)]), (-1, &[])]);
    let c_neg = p_neg.count_roots_in_interval(0, &rat(-2), &rat(2));
    let c_pos = p_pos.count_roots_in_interval(0, &rat(-2), &rat(2));
    assert_eq!(c_neg, 2);
    assert_eq!(c_pos, 2);
    assert_eq!(
        c_neg, c_pos,
        "root count must be independent of overall sign"
    );
}

/// A narrower interval isolating a single root must count 1.
#[test]
fn sturm_count_roots_single_root_interval() {
    // p = -x^2 + 1, interval (0, 2) contains only the root x = 1.
    let p = Polynomial::from_coeffs_int(&[(-1, &[(0, 2)]), (1, &[])]);
    let count = p.count_roots_in_interval(0, &rat(0), &rat(2));
    assert_eq!(count, 1);
}

/// Finding 2: `{x > 0, x < 0}` (no equalities) is unsatisfiable -- no real
/// number is simultaneously strictly positive and strictly negative. The old
/// code fell through to a fabricated `Sat`. The solver now has a real linear
/// decision procedure (`grobner::linear_arith::decide_linear_arms`, exact
/// Fourier-Motzkin elimination) wired into `check_sat`, so it genuinely
/// decides this system rather than merely refusing to say `Sat`: it must
/// report `Unsat`, the correct verdict.
#[test]
fn nra_linear_inequalities_not_wrongly_sat() {
    let mut solver = NraSolver::new();
    let x = Polynomial::from_var(0);
    solver.add_constraint(PolynomialConstraint::greater(x.clone())); // x > 0
    solver.add_constraint(PolynomialConstraint::less(x)); // x < 0

    let result = solver.check_sat();
    assert_ne!(
        result,
        SatResult::Sat,
        "unsatisfiable linear inequalities must never be reported Sat"
    );
    assert_eq!(
        result,
        SatResult::Unsat,
        "x > 0 and x < 0 is genuinely unsatisfiable and the solver now has a \
         linear decision procedure (Fourier-Motzkin) that proves it, so the \
         correct verdict is Unsat, not merely Unknown"
    );
}

/// A single non-constant linear inequality `x > 0` is satisfiable (e.g.
/// `x = 1`). The linear Fourier-Motzkin decision procedure now decides this
/// exactly instead of giving up with `Unknown`.
#[test]
fn nra_single_linear_inequality_is_decided_sat() {
    let mut solver = NraSolver::new();
    let x = Polynomial::from_var(0);
    solver.add_constraint(PolynomialConstraint::greater(x)); // x > 0
    assert_eq!(
        solver.check_sat(),
        SatResult::Sat,
        "x > 0 is satisfiable (witness x = 1); the linear decision \
         procedure must decide it, not fall back to Unknown"
    );
}

/// A genuinely non-linear leftover (`x^2 > 0`, degree 2) has no decision
/// procedure wired in (Fourier-Motzkin only handles the linear/affine
/// subset). The honest result is `Unknown` -- it must never be fabricated as
/// `Sat` (true for x != 0) or `Unsat` (never true).
#[test]
fn nra_nonlinear_inequality_still_honestly_unknown() {
    let mut solver = NraSolver::new();
    let x_squared = Polynomial::from_coeffs_int(&[(1, &[(0, 2)])]);
    solver.add_constraint(PolynomialConstraint::greater(x_squared)); // x^2 > 0
    assert_eq!(
        solver.check_sat(),
        SatResult::Unknown,
        "non-linear constraints have no decision procedure wired in; the \
         solver must say Unknown rather than guess"
    );
}

/// Constant inequalities are still fully decided (no regression).
#[test]
fn nra_constant_inequalities_still_decided() {
    // -1 > 0 is unsat.
    let mut solver = NraSolver::new();
    solver.add_constraint(PolynomialConstraint::greater(Polynomial::constant(rat(-1))));
    assert_eq!(solver.check_sat(), SatResult::Unsat);

    // 1 > 0 is sat.
    let mut solver2 = NraSolver::new();
    solver2.add_constraint(PolynomialConstraint::greater(Polynomial::constant(rat(1))));
    assert_eq!(solver2.check_sat(), SatResult::Sat);
}

/// Finding 3: when the reduction loop hits its iteration cap, the unreduced
/// tail must not be dropped. Build a 1200-term polynomial in x and reduce it
/// by a polynomial in y (nothing is reducible), forcing 1200 term-moves which
/// exceeds the internal 1000-iteration cap. The result must still equal the
/// input (it is ideal-equivalent), not a truncated polynomial.
#[test]
fn reduce_does_not_drop_tail_at_iteration_cap() {
    // f = sum_{k=0}^{1199} x^k
    let mut f = Polynomial::zero();
    for k in 0..1200u32 {
        f = f.add(&Polynomial::from_coeffs_int(&[(1, &[(0, k)])]));
    }

    // g = y (variable 1); no monomial of f (all in x) is divisible by y, so
    // reduce performs only term-moves and cannot actually reduce anything.
    let g = Polynomial::from_var(1);

    let reduced = reduce(&f, &[g]);

    // Ideal-equivalent and, since nothing reduces, literally equal to f.
    let diff = reduced.sub(&f);
    assert!(
        diff.is_zero(),
        "reduce() dropped part of the polynomial at the iteration cap"
    );
}
