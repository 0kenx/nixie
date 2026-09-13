//! Regressions for the wide-literal / integer-mode arithmetic defects found
//! by the TLA+ front end's encoder cross-check (2026-09-13) and fixed the
//! same week.  Every case here is builder-level (no TLA+ involved): see
//! `docs/studies/2026-09-13-lia-wide-literal-arithmetic.md` for the original
//! reproductions and the fix layering.
//!
//! Four defects, one root theme – *the width and integrality of arithmetic
//! were assumed instead of enforced*:
//!
//! 1. `(i64::MAX + 1) = i64::MAX + 1` PANICKED inside `num-rational`
//!    (`attempt to add with overflow`): the linear-parse accumulator summed
//!    two individually-`i64`-fitting literals into a `Ratio<i64>`.  In the
//!    release profile (`panic = "abort"`, no `overflow-checks`) the same
//!    arithmetic *silently wrapped* – a wrong-coefficient, wrong-verdict
//!    hazard, not just a crash.
//! 2. Above that, wide-literal arithmetic answered `Unknown`.
//! 3. `26 div 2 = 13` answered `Unknown` – the default arithmetic solver ran
//!    real mode, which refuses the Euclidean `div`/`mod` defining axioms.
//! 4. (Found while fixing 3, the most serious of all) `x:Int ∧ x>3 ∧ x<4`
//!    answered **`sat`** from the LP point `x = 3.5` – the default solver
//!    had no integrality at all, a false model on the most basic integer
//!    query.
//!
//! The fixes, layer by layer: exact `BigInt`/`BigRational` constant folding
//! in `TermManager`'s builders (Z3's `arith_rewriter` mk-time policy); a
//! mixed-integer default for `ArithSolver` with per-term integrality (Z3's
//! `theory_mi_arith`, the unset-logic mode); checked accumulation in the
//! linear parse with an honesty gate on overflow.

use nixie_core::TermManager;
use nixie_solver::{Solver, SolverResult};
use num_bigint::BigInt;

/// The negation of a valid claim must be unsat: `(a + 1) = a + 1` for a
/// literal `a`, across the `i64` boundary and far above it.
fn wide_sum_validity(lit: BigInt) -> SolverResult {
    let mut tm = TermManager::new();
    let a = tm.mk_int(lit.clone());
    let one = tm.mk_int(1);
    let sum = tm.mk_add([a, one]);
    let expected = tm.mk_int(lit + 1);
    let claim = tm.mk_eq(sum, expected);
    let negated = tm.mk_not(claim);
    let mut s = Solver::new();
    s.assert(negated, &mut tm);
    s.check(&mut tm)
}

#[test]
fn wide_literal_sum_at_i64_max_is_unsat() {
    // This exact call aborted the process before the fix.
    assert_eq!(
        wide_sum_validity(BigInt::from(i64::MAX)),
        SolverResult::Unsat
    );
}

#[test]
fn wide_literal_sum_boundaries() {
    assert_eq!(
        wide_sum_validity(BigInt::from(1i64 << 62)),
        SolverResult::Unsat
    );
    assert_eq!(
        wide_sum_validity(BigInt::from(i64::MAX - 1)),
        SolverResult::Unsat
    );
    // Used to be `Unknown` (big-const abstraction with no exactness).
    assert_eq!(
        wide_sum_validity(BigInt::from(2u32).pow(64) - 1),
        SolverResult::Unsat
    );
    assert_eq!(
        wide_sum_validity(BigInt::from(2u32).pow(96) - 1),
        SolverResult::Unsat
    );
}

/// Two big constants in one row, equal through a variable:
/// `(= (+ x 2^63) (+ x (+ i64::MAX 1)))` is valid; its negation is unsat.
/// Exercises the big-const column sharing between a literal and a folded sum.
#[test]
fn wide_folded_sum_and_wide_literal_agree_through_a_variable() {
    let mut tm = TermManager::new();
    let x = tm.mk_var("x", tm.sorts.int_sort);
    let lhs = {
        let c = tm.mk_int(BigInt::from(2u32).pow(63));
        tm.mk_add([x, c])
    };
    let rhs = {
        let max = tm.mk_int(i64::MAX);
        let one2 = tm.mk_int(1);
        let sum = tm.mk_add([max, one2]);
        tm.mk_add([x, sum])
    };
    let claim = tm.mk_eq(lhs, rhs);
    let negated = tm.mk_not(claim);
    let mut s = Solver::new();
    s.assert(negated, &mut tm);
    assert_eq!(s.check(&mut tm), SolverResult::Unsat);
}

/// `div`/`mod` on two literals constant-fold (Euclidean), so their valid
/// claims are decided.  `(26 div 2) = 13` used to be `Unknown` under the
/// default solver.
#[test]
fn literal_div_and_mod_are_decided() {
    let mut tm = TermManager::new();
    let a = tm.mk_int(26);
    let two = tm.mk_int(2);
    let d = tm.mk_div(a, two);
    let c13 = tm.mk_int(13);
    let claim = tm.mk_eq(d, c13);
    let mut s = Solver::new();
    s.assert(tm.mk_not(claim), &mut tm);
    assert_eq!(s.check(&mut tm), SolverResult::Unsat);

    let mut tm = TermManager::new();
    let a = tm.mk_int(26);
    let four = tm.mk_int(4);
    let m = tm.mk_mod(a, four);
    let c2 = tm.mk_int(2);
    let claim = tm.mk_eq(m, c2);
    let mut s = Solver::new();
    s.assert(tm.mk_not(claim), &mut tm);
    assert_eq!(s.check(&mut tm), SolverResult::Unsat);
}

/// A *variable* dividend under `div`/`mod` keeps its defining axioms under
/// the default (mixed-integer) solver: `(mod x 3) ∈ [0,3)`, so
/// `(> (mod x 3) 5)` is unsat.  This used to be `Unknown` because the
/// default ran real mode and refused the axioms.
#[test]
fn variable_dividend_mod_axioms_fire_under_default_solver() {
    let mut tm = TermManager::new();
    let x = tm.mk_var("x", tm.sorts.int_sort);
    let three = tm.mk_int(3);
    let m = tm.mk_mod(x, three);
    let five = tm.mk_int(5);
    let gt = tm.mk_gt(m, five);
    let mut s = Solver::new();
    s.assert(gt, &mut tm);
    assert_eq!(s.check(&mut tm), SolverResult::Unsat);
}

/// **The false-`sat` root**: an `Int` variable between two adjacent
/// integers.  The default solver used to be pure LRA, so `x = 3.5`
/// "satisfied" it; the mixed-integer default closes the hole.
#[test]
fn integer_variable_between_adjacent_integers_is_unsat() {
    let mut tm = TermManager::new();
    let x = tm.mk_var("x", tm.sorts.int_sort);
    let c3 = tm.mk_int(3);
    let c4 = tm.mk_int(4);
    let gt = tm.mk_gt(x, c3);
    let lt = tm.mk_lt(x, c4);
    let both = tm.mk_and([gt, lt]);
    let mut s = Solver::new();
    s.assert(both, &mut tm);
    assert_eq!(s.check(&mut tm), SolverResult::Unsat);
}

/// The same hole with a `Real` variable MUST stay `sat` – per-variable
/// integrality, not a global integer choke.
#[test]
fn real_variable_between_adjacent_integers_stays_sat() {
    let mut tm = TermManager::new();
    let y = tm.mk_var("y", tm.sorts.real_sort);
    let c3 = tm.mk_real(num_rational::Rational64::from_integer(3));
    let c4 = tm.mk_real(num_rational::Rational64::from_integer(4));
    let gt = tm.mk_gt(y, c3);
    let lt = tm.mk_lt(y, c4);
    let both = tm.mk_and([gt, lt]);
    let mut s = Solver::new();
    s.assert(both, &mut tm);
    assert_eq!(s.check(&mut tm), SolverResult::Sat);
}

/// Mixed Int/Real in ONE problem: `x:Int` keeps integrality while `y:Real`
/// stays continuous (`2x + y = 1 ∧ y = 0.5 ⇒ x = 1/4` – unsat).
#[test]
fn mixed_int_real_problem_tracks_each_variables_sort() {
    let mut tm = TermManager::new();
    let x = tm.mk_var("x", tm.sorts.int_sort);
    let y = tm.mk_var("y", tm.sorts.real_sort);
    let two_c = tm.mk_int(2);
    let two_x = tm.mk_mul([two_c, x]);
    let sum = tm.mk_add([two_x, y]);
    let one = tm.mk_real(num_rational::Rational64::from_integer(1));
    let eq = tm.mk_eq(sum, one);
    let half = tm.mk_real(num_rational::Rational64::new(1, 2));
    let pin = tm.mk_eq(y, half);
    let both = tm.mk_and([eq, pin]);
    let mut s = Solver::new();
    s.assert(both, &mut tm);
    assert_eq!(s.check(&mut tm), SolverResult::Unsat);
}

/// The accumulator-overflow class: nested `Sub` whose leaves fold but whose
/// constant sum (`i64::MAX + 1`) only assembles inside the linear parse.
/// The walk now accumulates the constant EXACTLY (`BigRational`) and
/// synthesizes the too-wide sum as a wide `IntConst` column (the existing
/// big-constant abstraction), so the atom parses, never wraps (release) or
/// panics (debug), and `sat` answers only through model certification.
///
/// What stays OUT OF REACH — deliberately, and recorded in the study — is
/// the *value-dependent refutation*: proving `(= (+ x MAX 1) (+ x 2^63))`
/// requires the tableau to reason at the value `2^63`, whose row
/// combinations and column values leave `Rational64` width.  Z3 decides
/// these because its tableau computes in `mpz`; Nixie's fixed-width LP has
/// that boundary, and the honest answer for it is `Unknown`, never a
/// wrapped verdict.  The assertions below pin exactly that contract.
#[test]
fn nested_constant_overflow_never_answers_wrongly() {
    let mut tm = TermManager::new();
    let x = tm.mk_var("x", tm.sorts.int_sort);
    let zero = tm.mk_int(0);
    let one = tm.mk_int(1);
    // `(0 - 1)` folds to `-1` at construction; the MAX + 1 sum happens in
    // `extract_linear_terms`.
    let neg_one = tm.mk_sub(zero, one);
    let maxc = tm.mk_int(i64::MAX);
    let x_max = tm.mk_add([x, maxc]);
    let lhs = tm.mk_sub(x_max, neg_one);
    let two63 = tm.mk_int(BigInt::from(2u32).pow(63));
    let rhs = tm.mk_add([x, two63]);
    let claim = tm.mk_eq(lhs, rhs); // valid: both sides are x + 2^63
    let mut s = Solver::new();
    s.assert(tm.mk_not(claim), &mut tm);
    let r = s.check(&mut tm);
    assert_ne!(
        r,
        SolverResult::Sat,
        "a valid claim's negation must never be Sat"
    );

    // The INVALID twin (`x + 2^63` vs `x + 2^63 + 1`): asserting the false
    // claim must never be `Sat`, and refuting the true negation... the
    // negation is valid so it must be Sat-or-Unknown, never Unsat.
    let two63p1 = tm.mk_int(BigInt::from(2u32).pow(63) + 1);
    let rhs2 = tm.mk_add([x, two63p1]);
    let false_claim = tm.mk_eq(lhs, rhs2); // the sides differ by 1
    let mut s2 = Solver::new();
    s2.assert(false_claim, &mut tm);
    assert_ne!(
        s2.check(&mut tm),
        SolverResult::Sat,
        "a false claim must never be Sat"
    );
    let mut s3 = Solver::new();
    s3.assert(tm.mk_not(false_claim), &mut tm);
    assert_ne!(
        s3.check(&mut tm),
        SolverResult::Unsat,
        "a valid claim's negation must never be Unsat"
    );
}

/// The `-2^63` corner: the value fits `i64` but its negation does not, so
/// it must travel as a (sign-flipped) big column, never as a fixed-width
/// constant that `row_key` or DL normalization would flip.  These ARE
/// decided — the corner only needed the parse-side handling.
#[test]
fn neg_two_pow_63_constant_is_decided() {
    let mut tm = TermManager::new();
    let x = tm.mk_var("x", tm.sorts.int_sort);
    let zero = tm.mk_int(0);
    // x = -2^63 is satisfiable (x is an Int).
    let wide = tm.mk_int(BigInt::from(2u32).pow(63));
    let neg_wide = tm.mk_sub(zero, wide);
    let claim = tm.mk_eq(x, neg_wide);
    let mut s = Solver::new();
    s.assert(claim, &mut tm);
    assert_eq!(s.check(&mut tm), SolverResult::Sat);
    // The same value built by folding `-i64::MAX - 1`, and the two wide
    // negatives are the SAME value.
    let maxc = tm.mk_int(i64::MAX);
    let one = tm.mk_int(1);
    let neg_max = tm.mk_sub(zero, maxc);
    let nm1 = tm.mk_sub(neg_max, one);
    let same = tm.mk_eq(neg_wide, nm1);
    let mut s3 = Solver::new();
    s3.assert(tm.mk_not(same), &mut tm);
    assert_eq!(s3.check(&mut tm), SolverResult::Unsat);
}

/// An equality whose coefficients all cancel leaves an EMPTY row; with a
/// FRACTIONAL constant (`0 = 5/3`) the infeasibility used to be dropped
/// silently — the contradictory bounds were planted only on
/// `expr.terms.first()`, which an empty row does not have — leaving the atom
/// a free Boolean and reporting `sat`.  Found by the mixed-mode fuzz right
/// after `/`-linearization made constant-folded dividends under `(/ x 3)`
/// reachable.
#[test]
fn empty_row_with_fractional_constant_is_refuted() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_LRA)(declare-const xr Real)\
             (assert (= (/ (+ (* 1 xr) (+ -85 (* 1 xr) (* -2 xr))) 3) -1099511627776))\
             (check-sat)",
        )
        .expect("script");
    assert_eq!(out[0], "unsat", "{}", out[0]);

    // The direct shape: xr - xr = 5/3 is false.
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(declare-const xr Real)(assert (= (- (* 1 xr) (* 1 xr)) (/ 5.0 3.0)))(check-sat)",
        )
        .expect("script");
    assert_eq!(out[0], "unsat", "{}", out[0]);
}

/// A wide constant assembled only in the linear parse (11x = i64::MAX + 24)
/// synthesizes a big column; the honesty gate must keep a spurious model from
/// being reported `sat` (the abstraction has no integer solution, but the
/// abstraction itself is satisfiable — only certification can tell).
#[test]
fn synthesized_wide_column_never_answers_wrongly() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_LIA)(declare-const xi Int)\
             (assert (and (= (+ -24 (* 1 xi) (* 10 xi)) 9223372036854775807)\
                          (<= (div (+ (+ (* 1 xi) -1099511627776) (mod 1 1)) 2) 3)\
                          (<= (+ (* 2 xi) (+ (+ 9 (* 1 xi)) (+ (* 2 xi) -8))) -4)))\
             (check-sat)",
        )
        .expect("script");
    // The truth: 11x = 2^63 + 23 has no integer solution (remainder 9),
    // so `unsat` is the right answer; `unknown` (uncertified abstraction)
    // is acceptable; `sat` is a wrong answer.
    assert_ne!(out[0], "sat", "{}", out[0]);
}
