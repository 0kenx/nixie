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

/// The strict-inequality tightening `k ± 1` is checked at the boundary:
/// `-x > i64::MAX` (satisfiable at `x = -2^63` — SMT `Int` is unbounded)
/// used to compute `MAX + 1` unchecked — a debug panic and a SILENT WRAP to
/// `i64::MIN` in release, a different constraint than the one asserted.  The
/// unshiftable bound now falls through to the exact delta-rational path.
#[test]
fn strict_tightening_at_the_i64_boundary_is_exact() {
    use nixie_solver::Context;
    for (script, want) in [
        // -x > MAX  ⟺  x < -MAX  ⟺  x ≤ -2^63 — satisfiable.
        (
            "(declare-const x Int)(assert (> (* -1 x) 9223372036854775807))(check-sat)",
            "sat",
        ),
        // x < i64::MIN is unsatisfiable only if Int were bounded; it is not,
        // so `x < i64::MIN` is satisfiable (any integer below MIN... there
        // is none — MIN is the smallest representable but SMT Int is
        // unbounded BELOW it too: satisfiable).
        (
            "(declare-const x Int)(assert (< x (- 9223372036854775807 1)))(assert (> x (- 9223372036854775807 1)))(check-sat)",
            "unsat",
        ),
    ] {
        let mut ctx = Context::new();
        let out = ctx.execute_script(script).expect("script");
        assert_eq!(out[0], want, "{script}: {}", out[0]);
    }
}

/// Wide-literal cancellation at the value layer (2026-09-15, the wide-LP
/// slice): coefficients and constants that each fit `i64` while their
/// row-value INTERMEDIATES do not (`2^62 · 2 = 2^63`), with finals that fit
/// after cancellation. The pivot's substitution, the entering-row build and
/// `intern_row`'s basic-substitution all used to decline (or, before the
/// checked era, wrap) on the intermediate; each now retries that derivation
/// in exact `BigRational` and narrows the final — the item-14 pattern
/// applied to the row/value layer. `v0 = 2^62·1 − 2^62·2 + 1 = 1 − 2^62`
/// fits, so the goal is decidable.
#[test]
fn wide_cancellation_value_is_decidable_sat() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_LRA)
             (declare-const v0 Real) (declare-const w Real) (declare-const u Real)
             (assert (= w 1)) (assert (= u 2))
             (assert (= v0 (+ (* 4611686018427387904 w) (* (- 0 4611686018427387904) u) 1)))
             (check-sat)",
        )
        .expect("script executes");
    assert_eq!(out.last().map(String::as_str), Some("sat"));
}

/// The refutation twin: the same wide-cancellation row against a wrong pin
/// — `v0 = 0` contradicts `v0 = 1 − 2^62`. Both verdict directions of the
/// slice must work at width.
#[test]
fn wide_cancellation_refutation_is_decidable_unsat() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_LRA)
             (declare-const v0 Real) (declare-const w Real) (declare-const u Real)
             (assert (= w 1)) (assert (= u 2))
             (assert (= v0 (+ (* 4611686018427387904 w) (* (- 0 4611686018427387904) u) 1)))
             (assert (= v0 0))
             (check-sat)",
        )
        .expect("script executes");
    assert_eq!(out.last().map(String::as_str), Some("unsat"));
}

/// A bound AT the cancelled width: `v0 > −2^62 − 1` holds for
/// `v0 = 1 − 2^62` — the comparison itself must not decline.
#[test]
fn wide_cancellation_bound_comparison_decides() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_LRA)
             (declare-const v0 Real) (declare-const w Real) (declare-const u Real)
             (assert (= w 1)) (assert (= u 2))
             (assert (= v0 (+ (* 4611686018427387904 w) (* (- 0 4611686018427387904) u) 1)))
             (assert (> v0 (- 0 4611686018427387905)))
             (check-sat)",
        )
        .expect("script executes");
    assert_eq!(out.last().map(String::as_str), Some("sat"));
}

/// The wide-row scaling (2026-09-15, wide-LP slice 3): a row whose finals
/// exceed `Rational64` is rescaled by a POSITIVE factor into width before
/// any wide-store capture — every constraint bound in this encoding is
/// ZERO, which a positive multiple preserves — so the 40-deep chain with
/// `i64::MAX` increments (constants combining to `≈ 2^102`, the odd
/// `3·i64::MAX` shapes needing odd-factor relief) now DECIDES both
/// directions, matching z3. This test pins the satisfiable side: the
/// chain plus `v0 = 1`, `v39 < 0` has a rational solution and the solver
/// must find it.
#[test]
fn wide_chain_is_decidable_sat_after_scaling() {
    use nixie_solver::Context;
    let mut lines = vec![
        "(set-logic QF_LRA)".to_string(),
        "(declare-const v0 Real)".to_string(),
    ];
    let n = 40usize;
    lines.extend((1..n).map(|i| format!("(declare-const v{i} Real)")));
    lines.push("(assert (= v0 1))".to_string());
    for i in 0..n - 1 {
        lines.push(format!(
            "(assert (= v{i} (+ (* 2 v{}) 9223372036854775807)))",
            i + 1
        ));
    }
    lines.push("(assert (< v39 0))".to_string());
    lines.push("(check-sat)".to_string());
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(&lines.join("\n"))
        .expect("script executes");
    assert_eq!(out.last().map(String::as_str), Some("sat"));
}

/// The honest wall that REMAINS: a row whose huge constant is a large
/// PRIME (no small odd factor to strip into the denominator) is
/// unrepresentable at every positive scale — the wide-store capture
/// applies, the convergence check cannot certify it, and the answer is
/// `unknown`, never a wrapped verdict. (2^100-scale primes exceed the
/// small-odd-factor relief of the scaler by construction.)
#[test]
fn large_prime_constant_rows_stay_honest() {
    use nixie_solver::Context;
    let mut lines = vec![
        "(set-logic QF_LRA)".to_string(),
        "(declare-const v0 Real)".to_string(),
        "(declare-const v1 Real)".to_string(),
    ];
    // 1267650600228229401496703205653 is prime (first prime above 2^100).
    lines.push("(assert (= v0 (+ (* 1267650600228229401496703205653 v1) 1)))".to_string());
    lines.push("(assert (= v0 0))".to_string());
    lines.push("(assert (> v1 0))".to_string());
    lines.push("(check-sat)".to_string());
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(&lines.join("\n"))
        .expect("script executes");
    let last = out.last().map(String::as_str).unwrap_or("");
    // v1 = -1/1267650600228229401496703205653 < 0 contradicts v1 > 0:
    // truly unsat; the honest answer without exact refutation is unknown.
    // A `sat` here would be an unverified witness; a `sat` with a VALID
    // model would be fine — but no rational model exists.
    assert_ne!(last, "sat", "the goal is unsatisfiable; sat would be wrong");
}

/// The wide-row side table (2026-09-15, wide-LP slice 2): a formula whose
/// chain rows combine past any `Rational64` (`≈ 2^102`) no longer declines
/// globally when a row goes wide — the row is captured exactly (pivoting
/// and propagation excluded from it, its value re-derived exactly), so the
/// formula's *other*, narrow constraints stay decidable. Here the two pins
/// on `v0` conflict through narrow rows alone: decided `unsat`, matching
/// z3, where the whole goal used to be an honest `unknown` because the
/// wide chain rows aborted the check.
#[test]
fn wide_chain_pins_conflict_is_decidable_unsat() {
    use nixie_solver::Context;
    let mut lines = vec![
        "(set-logic QF_LRA)".to_string(),
        "(declare-const v0 Real)".to_string(),
    ];
    let n = 40usize;
    lines.extend((1..n).map(|i| format!("(declare-const v{i} Real)")));
    lines.push("(assert (= v0 1))".to_string());
    lines.push("(assert (= v0 2))".to_string());
    for i in 0..n - 1 {
        lines.push(format!(
            "(assert (= v{i} (+ (* 2 v{}) 9223372036854775807)))",
            i + 1
        ));
    }
    lines.push("(check-sat)".to_string());
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(&lines.join("\n"))
        .expect("script executes");
    assert_eq!(out.last().map(String::as_str), Some("unsat"));
}

/// The exact-coefficient parse retry (2026-09-15, wide-LP slice 4): a
/// comparison whose COEFFICIENTS leave `i64` width is re-parsed with exact
/// `BigRational` coefficients (wide constants plain, no column
/// abstraction) and the whole row rescaled into width by a positive
/// factor — zero bounds are preserved, so the scaled row is the same
/// constraint. Uniform-magnitude wide rows (`2^63`-scale coefficients)
/// now decide BOTH directions where the parse used to gate them to
/// `unknown` (or, before item 32, drop them as free Booleans).
#[test]
fn uniform_wide_coefficients_decide_both_directions() {
    use nixie_solver::Context;
    let sat = r#"
        (set-logic QF_LRA)
        (declare-const a Real) (declare-const b Real)
        (assert (= a 1)) (assert (= b 0))
        (assert (= (+ (* 9223372036854775808 a) (* 9223372036854775810 b)) 9223372036854775808))
        (check-sat)"#;
    let mut ctx = Context::new();
    let out = ctx.execute_script(sat).expect("script executes");
    assert_eq!(out.last().map(String::as_str), Some("sat"));

    // 2^63·a − 2^63·b = 2^63 with a = b = 1 pins the LHS to 0 ≠ 2^63.
    let unsat = r#"
        (set-logic QF_LRA)
        (declare-const a Real) (declare-const b Real)
        (assert (= a 1)) (assert (= b 1))
        (assert (= (- (* 9223372036854775808 a) (* 9223372036854775808 b)) 9223372036854775808))
        (check-sat)"#;
    let mut ctx = Context::new();
    let out = ctx.execute_script(unsat).expect("script executes");
    assert_eq!(out.last().map(String::as_str), Some("unsat"));
}

/// The MIXED-magnitude wide row (`1` and `2^63` coefficients in one row)
/// parses and scales into the tableau, and the dual-width pivot (slice 5)
/// carries its entering row exactly in the wide store — so the
/// satisfiable twin now DECIDES (`v0 = 1` forces `v1 = 0`, a
/// representable value).
#[test]
fn mixed_magnitude_wide_row_sat_twin_decides() {
    use nixie_solver::Context;
    let sat_twin = r#"
        (set-logic QF_LRA)
        (declare-const v0 Real) (declare-const v1 Real)
        (assert (= v0 (+ (* 9223372036854775808 v1) 1)))
        (assert (= v0 1))
        (check-sat)"#;
    let mut ctx = Context::new();
    let out = ctx.execute_script(sat_twin).expect("script executes");
    assert_eq!(out.last().map(String::as_str), Some("sat"));
}

/// The unsat twin (`v0 = 0` forces `v1 = -2^-63`, contradicting
/// `v1 > 0`): the refutation needs chained bound reasoning through the
/// wide row (wide-row propagation — future work), so the honest
/// `unknown` applies. Pinned: never a `sat` (that is exactly the
/// wrong-verdict class item 32 closed).
#[test]
fn mixed_magnitude_wide_rows_stay_honest() {
    use nixie_solver::Context;
    let unsat_twin = r#"
        (set-logic QF_LRA)
        (declare-const v0 Real) (declare-const v1 Real)
        (assert (= v0 (+ (* 9223372036854775808 v1) 1)))
        (assert (= v0 0)) (assert (> v1 0))
        (check-sat)"#;
    let mut ctx = Context::new();
    let out = ctx.execute_script(unsat_twin).expect("script executes");
    let last = out.last().map(String::as_str).unwrap_or("");
    assert_ne!(
        last, "sat",
        "v1 = -2^-63 contradicts v1 > 0; sat would be wrong"
    );
}

/// The stale-assignment false-`unsat` (2026-09-15, root-caused from the f1
/// differential): `update_assignment` breaks early when a row's exact retry
/// overflows, leaving later rows' assignments stale, and the guard sites
/// forced `assignment_current = true` regardless — so after `check`'s
/// entry-time `resource_limit = false` cleared the only other witness, a
/// later pivot consumed the stale vector: the delta formula inherited the
/// stale base and (in release) a phony violation drove an invalid conflict.
/// A wrong `unsat` on a satisfiable mixed LIA goal with div/mod and wide
/// constants. The fix: `crash_basis` alone owns the flag, setting it from
/// `!resource_limit` — the flag may only say "current" through a FULL
/// successful derivation. This pins the honest verdict (never `unsat`;
/// the true answer is `sat`, and the overflow class declines honestly).
#[test]
fn stale_assignment_never_drives_false_unsat() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(include_str!(
            "../../docs/studies/assets/2026-09-15/false-unsat-f1.smt2"
        ))
        .expect("script executes");
    let last = out.last().map(String::as_str).unwrap_or("");
    // Strengthened 2026-09-16 (the value-overflow migration): a narrow row
    // whose exact VALUE leaves `Rational64` mid-search now migrates to the
    // wide store instead of declining the whole derivation — f1's
    // trajectory passes such a point and now converges to the model.
    assert_eq!(
        last, "sat",
        "the goal is satisfiable (z3 agrees); anything else is wrong or a lost capability"
    );
}

/// The wide-store value-fabrication false `sat` (2026-09-15, found by the
/// wide differential's fresh seeds): an `Int` variable whose defining row
/// lives in the wide store (the dual-width pivot) and whose exact value
/// `−9 − 41/2⁶³` does not narrow was read through the raw `assignment`
/// entry — a fabricated integral `0` — so branch-and-bound accepted the
/// LP point as a model and printed `v1 = 0` against a row forcing
/// `v1 = −9 − 41/2⁶³`: an invalid witness for an unsatisfiable goal.
/// The fix is layered: wide-aware exact value reads at every decision
/// site (`delta_value_exact`), branch bounds derived from the exact
/// UN-NARROWED value (`wide_floor_ceil_big` — floor/ceil of a 2⁶³-scale
/// rational are small integers, so the search stays decidable), an
/// underivable value declines to `Unknown`, and `Sat` is gated on every
/// term-backed variable having a derivable value. The exact branching
/// makes the goal DECIDABLY `unsat` (both branch directions are refuted
/// by the wide-row interval argument), matching z3.
#[test]
fn wide_basic_int_var_fabricated_value_never_drives_false_sat() {
    use nixie_solver::Context;
    let goal = r#"
        (set-logic QF_LIA)
        (declare-const v1 Int)
        (declare-const v2 Int)
        (assert (= (+ (* 27670116100584327436 v2) (* 9223372036854775808 v1)) -5))
        (assert (= v2 3))
        (check-sat)"#;
    let mut ctx = Context::new();
    let out = ctx.execute_script(goal).expect("script executes");
    let last = out.last().map(String::as_str).unwrap_or("");
    assert_ne!(last, "sat", "no integer v1 satisfies the row (z3: unsat)");
    assert_eq!(last, "unsat", "exact wide floor/ceil branching decides it");
}

/// The fuzz-original shape of the same defect (four variables, two wide
/// same-variable terms, pins on the decoys): pins the never-`sat` verdict.
#[test]
fn wide_coefficient_eq_row_with_pins_is_decidably_unsat() {
    use nixie_solver::Context;
    let goal = r#"
        (set-logic QF_LIA)
        (declare-const v0 Int)
        (declare-const v1 Int)
        (declare-const v2 Int)
        (declare-const v3 Int)
        (assert (= (+ (* 18446744073709551629 v2) (* 9223372036854775808 v1) (* 9223372036854775807 v2)) -5))
        (assert (= v2 3))
        (assert (= v3 -3))
        (assert (= v0 -2))
        (check-sat)"#;
    let mut ctx = Context::new();
    let out = ctx.execute_script(goal).expect("script executes");
    let last = out.last().map(String::as_str).unwrap_or("");
    assert_eq!(last, "unsat", "lhs ≡ 0 (mod 4) but rhs = −5 (z3: unsat)");
}

/// The wide-store narrow-back staleness false `unsat` (2026-09-15, the
/// delta-propagation canary's live find): a row captured into the wide
/// store (its exact value unrepresentable) keeps a FROZEN `assignment`
/// entry — the wide pass only re-derives narrowing values. When a later
/// pivot's substitution NARROWS the row back into the tableau, the commit
/// used to insert the row without recomputing the entry, and the snap
/// deltas then propagated from a stale base: a phony violation that (in
/// release) drove an invalid conflict — `unsat` on a satisfiable goal.
/// The fix: wide-origin rows are excluded from the delta loop and their
/// entry recomputed exactly at commit; a non-narrowing recomputation
/// defers through the staleness flag. This goal is `sat` (z3 agrees) with
/// the pins satisfying the wide row exactly.
#[test]
fn wide_row_narrow_back_recomputes_its_assignment_entry() {
    use nixie_solver::Context;
    let goal = r#"
        (set-logic QF_LIA)
        (declare-const v0 Int)
        (declare-const v1 Int)
        (declare-const v2 Int)
        (assert (<= (+ (* 9223372036854775808 v0) (* 576460752303423477 v2) (* 9223372036854775807 v2)) 9223372036854775810))
        (assert (= v2 -1))
        (assert (= v0 2))
        (assert (= v1 -2))
        (check-sat)"#;
    let mut ctx = Context::new();
    let out = ctx.execute_script(goal).expect("script executes");
    let last = out.last().map(String::as_str).unwrap_or("");
    assert_ne!(
        last, "unsat",
        "the pins satisfy the row (2·2⁶³ − 9799832789158199284 ≤ 9223372036854775810); z3: sat"
    );
}

/// The `static_features` collector's unchecked `i64` accumulation: two
/// same-variable `Mul` terms with huge constants (i64::MAX-scale against
/// a 2⁵⁹-scale) overflowed the `vars` coefficient map — a debug PANIC and
/// a release WRAP feeding garbage shape data to the routing layer. The
/// fix saturates (matching the file's existing `const_term`/`const_prod`
/// discipline): routing turns conservative, never wrong. This shape
/// previously aborted the debug binary before the solver even ran.
#[test]
fn static_features_wide_mul_accumulation_does_not_panic() {
    use nixie_solver::Context;
    let goal = r#"
        (set-logic QF_LIA)
        (declare-const v0 Int)
        (declare-const v1 Int)
        (declare-const v2 Int)
        (assert (<= (+ (* 9223372036854775808 v0) (* 576460752303423477 v2) (* 9223372036854775807 v2)) 9223372036854775810))
        (assert (= v2 -1))
        (assert (= v0 2))
        (assert (= v1 -2))
        (check-sat)"#;
    let mut ctx = Context::new();
    let out = ctx.execute_script(goal).expect("script executes");
    let last = out.last().map(String::as_str).unwrap_or("");
    assert_ne!(last, "", "a verdict must be produced, not an abort");
}

/// The strict-atom one-sided-endpoint false `unsat` (2026-09-16, round
/// three of the wide-row propagation): deriving a bound's SUPREMUM through
/// a variable with only a LOWER bound used the lone lower as the sup
/// endpoint — fabricating the tightest possible "upper". On the strict
/// `>` shape the atom slack's lone `(0, +1)` lower became a phony `−3−ε`
/// upper on the row's variable, crossed the real bounds, and refuted a
/// satisfiable goal. A one-sided pair now serves its own direction only
/// (a lone lower is an infimum; the supremum is +∞ — decline). Pinned
/// never-`unsat` (z3: `sat` at `v2 = 3`; the honest verdict without the
/// full propagation closure is `unknown`).
#[test]
fn strict_wide_row_one_sided_endpoint_never_drives_false_unsat() {
    use nixie_solver::Context;
    let goal = r#"
        (set-logic QF_LIA)
        (declare-const v2 Int)
        (assert (> (* 6927366777083328576 v2) -3))
        (assert (= v2 3))
        (check-sat)"#;
    let mut ctx = Context::new();
    let out = ctx.execute_script(goal).expect("script executes");
    let last = out.last().map(String::as_str).unwrap_or("");
    assert_ne!(last, "unsat", "6927366777083328576·3 > -3 holds; z3: sat");
}

/// The multi-term variant of the same class (the fuzz-original shape:
/// same-variable wide coefficients collected past `i64`, strict atom).
#[test]
fn strict_multi_term_wide_row_never_drives_false_unsat() {
    use nixie_solver::Context;
    let goal = r#"
        (set-logic QF_LIA)
        (declare-const v2 Int)
        (assert (> (+ (* 2305843009213693952 v2) (* 4611686018427387904 v2)) -3))
        (assert (= v2 3))
        (check-sat)"#;
    let mut ctx = Context::new();
    let out = ctx.execute_script(goal).expect("script executes");
    let last = out.last().map(String::as_str).unwrap_or("");
    assert_ne!(last, "unsat", "3·2^61·3 + 2^62·3 > -3 holds; z3: sat");
}

/// The item-54 false `unsat` (2026-09-17, found by the mixed differential,
/// seed 41): a QF_LIA three-disjunct `not(or …)` over `div`/`mod` with
/// `yi = 2^62` pinned.  The mechanism, decoded end to end: the atom
/// `3·yi < div(3·yi,1) + mod(3·yi,1)` (one trichotomy arm of the division
/// axiom's equality) interns its row `3yi − div − mod + 1`; the pin makes
/// the substituted constant `3·2^62 + 1` overflow `i64`, so `intern_row`
/// rescaled the row by `1/52` into width — sound for the zero BOUND
/// (`slack ≤ 0`), but the slack was still integer-marked from the
/// UNSCALED form.  A Gomory cut over that rescaled slack then fabricated
/// `52 | (1 − s_axiom)` — a divisibility constraint implied by nothing —
/// and refuted the division axiom ALONE (a conflict whose single reason
/// is the axiom, a theorem): `unsat` for a `sat` goal.  The fix
/// (`RowInternMode::Rescaled`) refuses the integer mark unless the
/// rescaled row is itself an integral form, so cuts and branch-and-bound
/// never reason from a fabricated integrality.
///
/// z3: `sat` (model `xi = 5, yi = 2^62`).  The current honest verdict is
/// `unknown` (the 2^62-scale width wall); the pin is the soundness
/// property: this goal may never answer `unsat`.
#[test]
fn rescaled_row_slack_never_drives_false_unsat() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(include_str!(
            "../../docs/studies/assets/2026-09-17/false-unsat-fi1.smt2"
        ))
        .expect("script executes");
    let last = out.last().map(String::as_str).unwrap_or("");
    assert_ne!(
        last, "unsat",
        "the goal is satisfiable (z3: sat at xi=5, yi=2^62); `unsat` is a fabricated refutation"
    );
}

/// The `i64::MIN`-bound corner (2026-09-17, found by the debug-panic sweep
/// on `QF_ANIA/diskperf`): `x < i64::MIN + 1` tightens to `x <= i64::MIN`,
/// whose row `x - rhs` needs the constant `+2^63` — the negation of
/// `i64::MIN` does not fit `Rational64`.  The unchecked `-rhs` PANICKED in
/// debug and silently WRAPPED in release, building a row for a DIFFERENT
/// constraint (`x + i64::MIN <= 0`).  The fix declines the assertion
/// through the sticky `unrepresentable_row_assert` flag: the goal answers
/// honest `unknown` (z3: `sat` at `x = i64::MIN`), never a wrapped
/// verdict.  The unsatisfiable twin is equally honest.
#[test]
fn i64_min_bound_rows_decline_instead_of_wrapping() {
    // The wide-LP build (2026-09-18) retired the sticky decline: every
    // `assert_*` entry whose `-rhs` leaves `Rational64` interns its row
    // EXACTLY (rescaled into width or captured in the wide store), so the
    // corner DECIDES where it used to answer honest `unknown`.  The
    // never-wrong contract this test guarded is STRENGTHENED into exact
    // verdicts (both z3-certified): the satisfiable side is `sat` (with a
    // model at `x = i64::MIN`), and the crossed pair refutes `unsat`
    // through the exact bound comparison.
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_LIA)\n\
             (declare-const x Int)\n\
             (assert (< x -9223372036854775807))\n\
             (check-sat)\n\
             (get-value (x))\n",
        )
        .expect("script executes");
    let last = out.last().map(String::as_str).unwrap_or("");
    assert_eq!(
        last, "((x -9223372036854775808))",
        "x = i64::MIN is the unique satisfying point (z3: sat there); any other value violates the bound"
    );
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_LIA)\n\
             (declare-const x Int)\n\
             (assert (and (< x -9223372036854775807) (> x -9223372036854775807)))\n\
             (check-sat)\n",
        )
        .expect("script executes");
    let last = out.last().map(String::as_str).unwrap_or("");
    assert_eq!(
        last, "unsat",
        "the crossed strict pair at the wall refutes exactly (z3: unsat); a wrapped row used to fabricate this, a decline used to block it"
    );
}

/// Wide-value publication (2026-09-17): a QF_LRA goal whose unique solution
/// is the exact rational `xr = -27670116110564327424/13` — the numerator
/// alone exceeds `i64`, so no `Rational64` assignment can hold it.  The LP
/// converges (the wide store knows the value exactly all along); the OLD
/// `wide_underivable_blocks_sat` gate declined the verdict because the
/// value did not NARROW — honest `unknown` for a decidable `sat`.  The
/// publication channel (`value_exact` + the `(/ n d)` term synthesis on
/// the model side) publishes the exact value, the certifier evaluates it
/// exactly, and the goal decides `sat`.  (The synthesis must build REAL
/// division: the first cut used `mk_div` — Euclidean — and get-value
/// printed the FLOOR, a published witness violating its own assertion;
/// caught by validating the model against z3.)
#[test]
fn wide_model_value_publishes_exactly_and_decides_sat() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_LRA)\n\
             (declare-const xr Real)\n\
             (assert (and (= (* 1 xr) (+ (+ (* 3 xr) (+ 9223372036854775807 0))\
                             (+ (- (* -2 xr) 3) (/ (* 10 xr) 3)\
                                (+ 2 (* 1 xr) 2))))))\n\
             (check-sat)\n\
             (get-value (xr))\n",
        )
        .expect("script executes");
    let verdict = out.first().map(String::as_str).unwrap_or("");
    assert_eq!(
        verdict, "sat",
        "the LP converges and the exact value publishes (z3: sat); `unknown` is a lost verdict"
    );
    let value = out.last().map(String::as_str).unwrap_or("");
    assert!(
        value.contains("27670116110564327424"),
        "the published model value must be the EXACT rational (numerator          -27670116110564327424 over 13), not a default or a floor: {value:?}"
    );
}

/// The B&B dead-leaf class (2026-09-17, the unsat-side gap survey's dive
/// site): `11·xi = 7` written through a `div`-by-1 feed — the search
/// branches to an all-integral candidate whose LP point is feasible, but
/// the leaf probe (`state_feasible`) re-derives through the bound-snap
/// `crash_basis` — a CRUDE point, not the search's vertex — lands outside
/// the windows, and the old code unwound the WHOLE search to `unknown`.
/// The leaf now re-solves (converging repairs the crude point; a
/// refutation is a DEAD BRANCH whose backtrack tries the siblings, and an
/// all-dead tree answers `unsat`).
#[test]
fn bnb_dead_leaf_backtracks_instead_of_unwinding_unknown() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(declare-const xi Int)\n\
             (assert (= (* -1 xi) (+ 1 -8 (div (* 10 xi) 1))))\n\
             (check-sat)\n",
        )
        .expect("script executes");
    let last = out.last().map(String::as_str).unwrap_or("");
    assert_eq!(
        last, "unsat",
        "xi = 7/11 is not integral (z3: unsat); `unknown` unwinds a repairable leaf"
    );
}

/// A `div` by a constant 1 over a SYMBOLIC dividend folds to its identity
/// (`div(t,1)=t`) at construction, removing the term from the div-axiom
/// feed: this pure-equality LIA goal (`15·xi + 3·zi = -52` once the
/// `div(-xi,1)` folds) is refutable by the GCD argument alone, but with the
/// `Div` node present the axiom feed hid the equality's coefficient
/// structure and the goal answered honest `unknown` (z3: `unsat`).
///
/// Found by the gap survey (seed 20261002, instance 567); the ±1-divisor
/// identity folds recovered 3 of the 7 UNSAT-side members on the fixed
/// survey seeds (plus 18 SAT-side — the feed was also deflecting searches).
#[test]
fn div_by_one_folds_and_the_gcd_refutation_decides() {
    let mut tm = TermManager::new();
    let xi = tm.mk_var("xi", tm.sorts.int_sort);
    let zi = tm.mk_var("zi", tm.sorts.int_sort);
    let ten = tm.mk_int(10);
    let five = tm.mk_int(5);
    let neg_two = tm.mk_int(-2);
    let three = tm.mk_int(3);
    let neg_one = tm.mk_int(-1);
    let one = tm.mk_int(1);
    let t10 = tm.mk_mul([ten, xi]);
    let t5 = tm.mk_mul([five, xi]);
    let tm2 = tm.mk_mul([neg_two, xi]);
    let t3z = tm.mk_mul([three, zi]);
    let neg_xi = tm.mk_mul([neg_one, xi]);
    // (div (* -1 xi) 1): folds to (* -1 xi) at construction.
    let d1 = tm.mk_div(neg_xi, one);
    let sum = tm.mk_add([t10, t5, tm2, t3z, d1]);
    let rhs = tm.mk_int(-52);
    let claim = tm.mk_eq(sum, rhs);
    let mut s = Solver::new();
    s.assert(claim, &mut tm);
    assert_eq!(s.check(&mut tm), SolverResult::Unsat);
}

/// The item-69 false `unsat` (2026-09-18, seed-20261102 mixed-fuzz instance
/// 17; bytes preserved under `docs/studies/assets/2026-09-18/`).  z3: `sat`;
/// nixie answered `unsat` from the first commit that had the machinery
/// (`5c8bf7a8`) through `ee8caf48`.
///
/// Root cause (the completion of study item 70's decode): the writer of the
/// unsound `hi = 7/20` was `rehome_stranded_row_bounds` -> `copy_bounds`.
/// The sweep re-interned a stranded slack's recorded form and copied the OLD
/// slack's live bound VALUES onto the fresh row.  After a pivot consumed the
/// old row, the fresh row renders the form through the *current* tableau -
/// which resolved it as `(20/7)*old`, a RESCALED multiple of the old slack
/// itself (the rescale factor item 70 fingered, dropped on exactly one side
/// by the value copy) - while the old slack's propagated pin said
/// `old = 7/20`.  The value-for-value copy then asserted `(20/7)*old = 7/20`
/// un-translated, a constraint nobody derived; it crossed the sound
/// `old = 7/20` derivation, and the crossing exported a SINGLETON conflict
/// blaming one Euclidean `div`/`mod` identity axiom - a learned unit
/// negated axiom that collapsed the search to `unsat`.
///
/// The sweep now only re-asserts the ATOM's own zero bound (scale-invariant,
/// and only for slacks no live row references at all); the instance decides
/// `sat`.
/// UN-IGNORED 2026-09-18: the derivation stamps (row-level incremental
/// propagation, landed in `010f0e7e`) removed the redundant re-derivation
/// that made this ~1180 s (see
/// `docs/studies/2026-09-18-rehome-wide-rational-blowup.md`), and the
/// checked branch-range subtraction closed the debug-profile overflow the
/// new trajectory exposed — ~80 s in this profile now. Still slow enough
/// to deserve its raised budget below.
#[test]
fn rehome_does_not_fabricate_a_crossing_on_a_referenced_slack() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_LIRA)\n\
             (declare-const xi Int)\n\
             (assert (and (not (or (= (mod (* 1 xi) 4) (div (- (+ 60 (* 2 xi) 20) 3) 3)) (not (and (>= (+ (+ (+ 2147483648 (* 3 xi) (* 3 xi)) (+ (* 2 xi) (* -1 xi) 62) (+ -92 (* -2 xi))) (+ (+ -2147483648 -4611686018427387904) (* 2 xi) (mod 5 7))) (mod (* 10 xi) 7)) (>= (mod (- (div (* 1 xi) 7) 2) 5) -6))) (not (or (> (mod (mod (* 3 xi) 5) 5) 71) (> (* 5 xi) 1) (< (+ (+ (+ (* 2 xi) (* 1 xi)) (+ -1 (* -2 xi) (* -1 xi)) (* 10 xi)) (+ (mod (* 2 xi) 1) (- (* 1 xi) 3) (+ 2 -5 6)) (* 10 xi)) (+ (+ (+ (* -2 xi) (* 2 xi)) (mod (* -2 xi) 1) -7) (+ (div (* 3 xi) 7) (+ (* 2 xi) (* 5 xi) (* 3 xi)))))))))))\n\
             (check-sat)\n"
        )
        .expect("script executes");
    let last = out.last().map(String::as_str).unwrap_or("");
    assert_eq!(
        last, "sat",
        "the full instance is satisfiable (z3 model xi = 658812288346769706);          `unsat` is the item-69 fabricated singleton-conflict false refutation"
    );
}

/// The same defect's TWO-disjunct core - the shape that still answered
/// `unsat` when the handoff shrank it (D1 alone, D1+C1 and D1+C2 all decided
/// correctly; the wrongness needed both C1 and C2).  Kept as a second pin so
/// a future regression in either the stranding gate or the atom-bound
/// re-assertion trips at the smaller shape too.
#[test]
fn rehome_false_unsat_seed_20261102_core_decides_sat() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_LIRA)\n\
             (declare-const xi Int)\n\
             (assert (not (or (= (mod (* 1 xi) 4) (div (- (+ 60 (* 2 xi) 20) 3) 3)) (not (and (>= (+ (+ (+ 2147483648 (* 3 xi) (* 3 xi)) (+ (* 2 xi) (* -1 xi) 62) (+ -92 (* -2 xi))) (+ (+ -2147483648 -4611686018427387904) (* 2 xi) (mod 5 7))) (mod (* 10 xi) 7)) (>= (mod (- (div (* 1 xi) 7) 2) 5) -6))))))\n\
             (check-sat)\n"
        )
        .expect("script executes");
    let last = out.last().map(String::as_str).unwrap_or("");
    assert_eq!(
        last, "sat",
        "the two-disjunct core is satisfiable (z3: sat); `unsat` is the item-69 defect"
    );
}

/// The seed-20261130 false `unsat` (found by the mixed differential's
/// fresh seeds one day after item 69 closed; mixed-fuzz instance, z3 `sat`).
///
/// Root cause: the slice-6 endpoint selector picked a two-sided bound pair's
/// side by COMPARING VALUES (`want_min == a_first`).  For an equal pair - a
/// pin whose two sides can carry DIFFERENT reason sets (the atom's own
/// assert on one side, a propagated bound on the other) - the tie-break
/// resolved to the OPPOSITE side: a min derivation cited the UPPER's
/// reasons and a max derivation the LOWER's.  Here `hi(v) = 0`, justified
/// only by the `(= 2 (mod (mod 3xi 2) 7))` trichotomy pin, was attributed
/// to the `(< 2 X)` atom's bound - which implies only `X <= 2` - and the
/// crossing then exported the PAIR `{(< 2 X), (> 2 X)}` as refuted when the
/// true refutation needed the equality atom: a learned clause eliminating
/// the satisfiable region where `X <= 1`.
///
/// The selector now picks by SIDE (each side is an independently live
/// fact), which is sound for crossed windows too.  Shrunk from the raw
/// instance by delta-debugging on (z3 sat, nixie unsat).
#[test]
fn equal_pin_endpoint_reasons_cite_their_own_side() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_LIRA)\n\
             (declare-const xi Int)\n\
             (assert (and (not (and (or (<= (+ (* 1 xi) (* -2 xi) (* -1 xi)) 4611686018427387904) (< (+ (+ 8 (div (* -2 xi) 5)) (+ (* -2 xi) (+ (* 1 xi) -7))) 7) (>= (+ (* 10 xi) (mod (+ (* 2 xi) (* -2 xi) (* -2 xi)) 1) (+ 93 (+ (* 2 xi) (* -2 xi) -51))) 0)) (and (> (+ (mod (+ (* -1 xi) -4 (* 1 xi)) 4) (* 1 xi) 1) (- (- (div (* 3 xi) 4) 3) 2)) (< (+ (+ (+ (* 1 xi) (* -2 xi)) (+ -3 (* 1 xi) (* 5 xi))) (* 5 xi) (+ (+ (* 10 xi) (* 1 xi)) (+ 85 -3) (* 2 xi))) 0)) (and (> (* -1 xi) 3) (< (+ (div (div (* 2 xi) 4) 1) (div (+ (* -2 xi) (* 2 xi)) 2) (* 10 xi)) (* 5 xi)) (> (- (+ -5 1099511627776 (+ (* 3 xi) (* 1 xi) (* -2 xi))) -2) 3)))) (not (and (not (and (< (mod (* -2 xi) 1) (+ (- 9 3) (* -2 xi) (* 10 xi))) (= (* 5 xi) (div (mod -8 1) 1)) (> (+ (+ 0 (div (* 5 xi) 7)) (+ -84 (* 2 xi)) (mod (+ (* 1 xi) (* 5 xi) 2147483647) 3)) 3))) (> (mod (mod (+ (* -1 xi) (* 3 xi) (* 2 xi)) 2) 7) 0) (<= (mod (+ (+ 59 23) (+ (* 2 xi) (* -1 xi)) (* 10 xi)) 7) -7))) (not (or (not (or (> (* 2 xi) 3) (< (+ (+ 0 (div -2 4)) (+ (+ (* 5 xi) 7) (+ (* 1 xi) 2) (* -2 xi)) (+ (mod (* -2 xi) 5) (* 5 xi))) 18) (> 9 2))) (not (or (<= (+ (div (* 3 xi) 1) (* 10 xi)) (mod (* 3 xi) 1)) (> (+ (+ (- 7 2) (* -2 xi)) (+ (mod -6 4) (* 5 xi) -9)) 1) (> (* 10 xi) 2)))))))\n\
             (check-sat)\n"
        )
        .expect("script executes");
    let last = out.last().map(String::as_str).unwrap_or("");
    assert_eq!(
        last, "sat",
        "the instance is satisfiable (z3: sat); `unsat` is the endpoint reason-side swap"
    );
}

// ---------------------------------------------------------------------------
// The wide-LP build (2026-09-18, the exact-arithmetic handoff): the bound
// store widened to exact values (`BoundValue`), the assert entries' exact
// row intern retiring the sticky decline, the B&B branch channel widened
// (`wide_floor_ceil_exact`), and the model-verification evaluator's exact
// numeric channel (`EvalVal::NumBig`).  The width walls this file's earlier
// entries documented as honest `unknown`s become decidable.
// ---------------------------------------------------------------------------

/// The handoff's example case, pinned with its MODEL: `xr < -2^63` over
/// QF_LRA is satisfiable at any rational below `-2^63` — a value that does
/// not fit `Rational64`, so the model publication must go through the
/// EXACT delta-instantiation channel (`value_exact` +
/// `delta_instantiation_exact`).  The pre-fix behavior was a debug PANIC in
/// `ArithSolver::value`'s unchecked instantiation sum (a release wrap to a
/// dishonest `+2^63`-scale witness that the certifier then rejected,
/// degrading the verdict to `unknown`).
#[test]
fn i64_min_real_strict_bound_decides_with_exact_model() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_LRA)\n\
             (declare-const xr Real)\n\
             (assert (< xr (/ (- 9223372036854775808) 1)))\n\
             (check-sat)\n\
             (get-value (xr))\n",
        )
        .expect("script executes");
    assert_eq!(
        out.first().map(String::as_str),
        Some("sat"),
        "any rational below -2^63 satisfies the bound (z3: sat)"
    );
    // The published witness must be BELOW -2^63 — the exact instantiation
    // of the strict bound `-2^63 - δ₀`.  (Validated against z3 by binding
    // the model as a define-fun and re-solving: z3 agrees `sat`.)
    let val = out.get(1).map(String::as_str).unwrap_or("");
    assert!(
        val.contains("-9223372036854775810") || val.contains("-9223372036854775809"),
        "the witness must be an exact rational strictly below -2^63, got: {val}"
    );
}

/// `x < i64::MIN` over QF_LIA: the `k - 1` tightening cannot run (it would
/// leave `i64`), so the strict delta path carries the constraint and the
/// integral model value `-2^63 - 1` publishes through the exact channel.
#[test]
fn i64_min_int_strict_bound_publishes_exact_witness() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_LIA)\n\
             (declare-const xi Int)\n\
             (assert (< xi (- 9223372036854775808)))\n\
             (check-sat)\n\
             (get-value (xi))\n",
        )
        .expect("script executes");
    assert_eq!(out.first().map(String::as_str), Some("sat"));
    assert_eq!(
        out.get(1).map(String::as_str),
        Some("((xi -9223372036854775809))"),
        "the least satisfying integer is -2^63 - 1 (z3's model); the raw \
         real part alone would publish -2^63, violating the strict bound"
    );
}

/// The evaluator's boundary negation: `(-x > i64::MAX)` at the honest model
/// `x = i64::MIN` requires evaluating `-i64::MIN = 2^63`.  The width-limited
/// channel reported `Unrepresentable`, the gate blocked its own correct
/// model as nongenuine, and the goal degraded to `unknown`; the exact
/// numeric channel (`EvalVal::NumBig`) evaluates the comparison and
/// certifies.
#[test]
fn boundary_negation_certifies_the_min_valued_model() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(declare-const x Int)\n\
             (assert (> (* -1 x) 9223372036854775807))\n\
             (check-sat)\n\
             (get-value (x))\n",
        )
        .expect("script executes");
    assert_eq!(out.first().map(String::as_str), Some("sat"));
    assert_eq!(
        out.get(1).map(String::as_str),
        Some("((x -9223372036854775808))"),
        "x = i64::MIN is the greatest satisfying point (z3: sat there)"
    );
}

/// A wide-published model value through the model formatter: the exact
/// rational is synthesized as a division term, which `get-model` must print
/// as a VALUE (the `?` placeholder this used to fall through to is not a
/// value at all).
#[test]
fn exact_model_values_print_as_values() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_LRA)\n\
             (declare-const xr Real)\n\
             (assert (< xr (/ (- 9223372036854775808) 1)))\n\
             (check-sat)\n\
             (get-model)\n",
        )
        .expect("script executes");
    assert_eq!(out.first().map(String::as_str), Some("sat"));
    let model = out.get(1).map(String::as_str).unwrap_or("");
    assert!(
        !model.contains('?'),
        "the model must print a concrete value for xr, got: {model}"
    );
}

/// The certification wall slice: `2^62`-scale arithmetic under the gate.
/// `(>= (+ x x) 0)` at `x = 2^62` evaluates `2^63 >= 0` — the exact fold
/// certifies the boundary model where the width-limited evaluator conceded
/// (the `no_certifiable_candidate` class; z3: sat).
#[test]
fn boundary_scale_sum_bound_certifies() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_LIA)\n\
             (declare-const x Int)\n\
             (assert (= x 4611686018427387904))\n\
             (assert (>= (+ x x) 0))\n\
             (check-sat)\n",
        )
        .expect("script executes");
    assert_eq!(
        out.first().map(String::as_str),
        Some("sat"),
        "2*(2^62) = 2^63 >= 0 holds exactly (z3: sat)"
    );
}

// ===========================================================================
// The floating-constant campaign (2026-09-19): the big-const column
// abstraction's column PINNED to its exact value, the fractional
// numerator-column extension, and the wide-point honest-value reads.
//
// Root cause chain (the gap survey's float slice, 8 of 47 members, plus the
// parse-gated fractional class, 9 more):
//   * a folded constant that leaves `Rational64` width in every orientation
//     became a FREE COLUMN (encode's abstraction) that floated — the model
//     published defaults, the evaluator refuted them, and the blocking loop
//     degraded a decidable `sat` to `unknown`;
//   * no λ = ±1/2^k can EVER shrink a numerator (it only cancels factors of
//     two), so a fractional beyond-width constant (`-15.4` summed against a
//     `2^62`-scale integer) had NO representable form at all — the parse
//     gated the atom to `Unknown`;
//   * `value()`'s honesty guard covered wide ROWS but not wide POINTS, so a
//     branch-and-bound bound at `2^63` scale published the stale `0`.
//
// The fixes: `ArithSolver::pin_int_const` (exact singleton bounds, tautology
// reason), the `−1/d`-coefficient numerator column, and the wide-point
// honest read.  Every model below is z3-validated (bind as `define-fun`s,
// negate the assertion, re-solve: `unsat`).

/// The motivating case: `3·xi + (i64::MAX + 2147483647 + 1) ≤ 7`, the
/// constant `9223372039002259453` far beyond width.  The synthesized column
// is pinned, the branch-and-bound drives xi to the true bound
/// `xi = -3074457346334086482` (z3's model), and the verdict is `sat` —
/// pre-fix this answered `unknown` through the refuted-model blocking loop.
#[test]
fn pinned_big_const_column_decides_sat() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(declare-const xi Int)\n\
             (assert (<= (+ (+ 9223372036854775806 2147483647) (* 3 xi)) 7))\n\
             (check-sat)\n\
             (get-value (xi))\n",
        )
        .expect("script executes");
    assert_eq!(out.first().map(String::as_str), Some("sat"), "z3: sat");
    let model = out.get(1).map(String::as_str).unwrap_or("");
    assert!(
        model.contains('-') && model.contains("3074457346334086482"),
        "xi rests at the true bound -3074457346334086482 (z3's model), got: {model}"
    );
}

/// A FRACTIONAL beyond-width constant: `-4611686018427387904 + 15.4` folds
/// to `-23058430092136939443/5`, whose numerator leaves `i64` and whose
/// oddness defeats every λ.  The numerator-column abstraction carries it
/// (`col ↦ 23058430092136939443` at coefficient `-1/5`, pinned), the verdict
/// is `sat`, and the model is EXACT: `xr = 7686143364045646481/10` — the
/// tight boundary value, z3-validated by negation.
#[test]
fn fractional_wide_constant_decides_with_exact_model() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(declare-const xr Real)\n\
             (assert (<= (+ -4611686018427387904 (* 6 xr)) -15.4))\n\
             (check-sat)\n\
             (get-value (xr))\n",
        )
        .expect("script executes");
    assert_eq!(out.first().map(String::as_str), Some("sat"), "z3: sat");
    let model = out.get(1).map(String::as_str).unwrap_or("");
    assert!(
        model.contains("7686143364045646481"),
        "xr = 7686143364045646481/10 exactly (the tight boundary, z3-validated), got: {model}"
    );
}

/// The column SIGN convention: the column replaces the moved-to-RHS
/// constant, so it must enter the row at `coef·col = −moved`.  The first
/// version of the numerator column entered at `+moved` and this exact shape
/// — satisfiable, z3 `sat` — answered `unsat` (a FALSE refutation: the row
/// asserted the negated constant, which against `5·xr > 4` is genuinely
/// infeasible).  Pins the convention for BOTH the fractional and the
/// integer arms.
#[test]
fn constant_column_sign_convention_is_not_inverted() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_LIRA)\n\
             (declare-const xi Int)\n\
             (declare-const yi Int)\n\
             (declare-const zi Int)\n\
             (declare-const xr Real)\n\
             (assert (and (and (= (+ (* 1 xr) 5 (+ (+ (* 3 xi) (* 10 xr)) (+ (* -2 zi) (* 3 zi) (* 1 xr)))) (div (* 3 zi) 3)) (or (> (* 2 zi) -4) (>= (+ (+ (mod 74 5) (- (* 1 xi) -2) 1099511627776) (+ (+ (* 1 xr) -2147483648 -31) (- (* 5 zi) 3) (+ (* 1 yi) (* 3 xi))) -3) -3.5))) (not (or (not (or (>= (mod (- (mod (* 1 zi) 2) 2) 2) (+ (+ (+ (* -2 xr) (* 1 xr)) (div 6 3) 78) (+ (+ -1 82) (* 1 xi) (+ -4 (* -2 xi))))) (<= (+ (+ -4611686018427387904 (+ (* 3 xr) (* 1 xr) (* -2 xr))) (/ (/ (* 2 xr) 4) 3)) -15.4))) (> -9 3) (not (and (> (* 5 xr) 4) (<= -4 (/ (+ (div (* 1 xi) 7) (* 10 xr)) 4))))))))\n\
             (check-sat)\n",
        )
        .expect("script executes");
    assert_eq!(
        out.first().map(String::as_str),
        Some("sat"),
        "z3: sat; an `unsat` here is the inverted-constant-column false refutation"
    );
}

/// A branch-and-bound bound beyond width parks an integer at a WIDE POINT;
/// its raw `assignment` entry is stale by design.  The model must publish
/// the EXACT point (`xi = -9223372036854775832`, z3-validated by negation) —
/// the stale `0` was refuted by the evaluator and degraded the verdict.
#[test]
fn wide_point_model_publication_is_exact() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(declare-const xr Real)\n\
             (declare-const xi Int)\n\
             (assert (<= (+ (+ (+ (* 1 xr) (* 3 xr)) (+ 5 (* -1 xi))) (+ (- 4611686018427387905 (- -2 0)) (* 1 xi)) (+ (+ (* 1 xi) (* -2 xi)) (+ 4611686018427387905 (* 2 xi)))) -14.6))\n\
             (check-sat)\n\
             (get-value (xi))\n",
        )
        .expect("script executes");
    assert_eq!(out.first().map(String::as_str), Some("sat"), "z3: sat");
    let model = out.get(1).map(String::as_str).unwrap_or("");
    assert!(
        model.contains("9223372036854775832"),
        "xi = -9223372036854775832 exactly (z3-validated), never the stale 0; got: {model}"
    );
}

/// The pin is SCOPED: bounds pop with the asserting level, and the atom's
/// re-assertion after a pop must re-pin (idempotent by bound inspection —
/// a parse-time memo would skip the re-pin and float the column again).
#[test]
fn pinned_column_repins_after_pop() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(declare-const xi Int)\n\
             (push 1)\n\
             (assert (<= (+ (+ 9223372036854775806 2147483647) (* 3 xi)) 7))\n\
             (pop 1)\n\
             (assert (<= (+ (+ 9223372036854775806 2147483647) (* 3 xi)) 7))\n\
             (check-sat)\n\
             (get-value (xi))\n",
        )
        .expect("script executes");
    assert_eq!(out.first().map(String::as_str), Some("sat"), "z3: sat");
    let model = out.get(1).map(String::as_str).unwrap_or("");
    assert!(
        model.contains("3074457346334086482"),
        "the re-pinned column still drives xi to the true bound, got: {model}"
    );
}

/// The B&B leaf's re-solve-vs-scan vertex mismatch (2026-09-19, found by
/// the boundary-literal SHAPES in the mixed differential, seed 20262113
/// instance 41): `mod(−2y + 2^62, 4) > 2` is UNSATISFIABLE — the
/// expression is always 0 or 2 — but the branch-and-bound leaf accepted a
/// model.  Mechanism: `find_fractional_int_var` scanned the *crude*
/// post-pop point and found every integer variable integral; the leaf's
/// feasibility `check()` then re-optimized onto a DIFFERENT vertex where
/// `q = (div (−2y + 2^62) 4)` sits at `(2^62−1)/4` — fractional — and the
/// snapshot published that vertex as a model, which the gate's
/// settled-atom arm had no chance against (the mod atom's committed
/// polarity is exactly what the bad feed justified).  The fix re-scans
/// integrality AT the re-solved vertex (`try_eq_incumbent`'s discipline);
/// the verdict is the honest `unknown` (z3: `unsat` — the parity refutation
/// `2y + 4q = 2^62 − 3` is beyond this build's wide-constant Diophantine
/// reach), never a `sat` with a fractional-vertex model.
#[test]
fn bnb_leaf_rescan_rejects_post_resolve_fractional_vertex() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_LIA)\n\
             (declare-const yi Int)\n\
             (assert (> (mod (+ (* -2 yi) 4611686018427387904) 4) 2))\n\
             (check-sat)\n",
        )
        .expect("script executes");
    assert_ne!(
        out.first().map(String::as_str),
        Some("sat"),
        "the goal is unsatisfiable (mod(−2y+2^62, 4) is always 0 or 2, never > 2); \
         `sat` here is a published model violating its own assertion"
    );
    // The honest verdict for this build; if a future Diophantine reach
    // closes the wide-constant parity class, `unsat` is also correct —
    // the pin is never-`sat`.
}

/// The wide-row interval refutation's SIGN (2026-09-19, the S3 residual's
/// dominant mechanism — 19 of the 110 survey members at `bf9f5b71`): for a
/// negative coefficient the row's minimum contribution is `+ c·hi` (the
/// endpoint choice folds the sign), but the accumulation SUBTRACTED it,
/// computing a range wider than the truth.  Valid refutations were missed
/// (conservative — the widened range can only fail to refute), the repair
/// step then found every direction blocked at its bound (NOCOL), and the
/// check declined LP-infeasible states to `unknown`.  This instance's
/// violated wide row (a `div`/`mod`-fractional row over a variable resting
/// at a `-4.6e18` upper) is genuinely refutable at its minimum — z3 and
/// the fixed build answer `sat` with `xi = 9` (model z3-validated); the
/// pre-fix build answered `unknown`.
#[test]
fn wide_row_interval_refutation_sign() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_LIA)\n\
             (declare-const xi Int)\n\
             (assert (and (or (<= (- -3 3) (+ (div (* -1 xi) 3) (div (mod -7 3) 3) (+ (mod (* -2 xi) 5) (+ (* 2 xi) -6)))) (>= (* 1 xi) 1099511627776)) (not (and (<= (+ (- (mod 9 7) 2) (+ (+ (* 1 xi) (* -2 xi)) (+ (* 10 xi) (* 5 xi)) (mod (* 1 xi) 7))) -3) (not (and (>= (* 1 xi) -4) (= xi 9223372036854775809))) (and (<= -96 5) (> (* -1 xi) 0) (= (+ (+ -73 (+ (* 1 xi) (* 1 xi)) (* 5 xi)) 7 2147483648) (+ (* 1 xi) (+ (+ (* 2 xi) (* -2 xi)) (+ -7 5) (- (* 10 xi) -2))))))) (> (+ (mod (- -7 3) 1) (div (* 3 xi) 2)) 4)))\n\
             (check-sat)\n",
        )
        .expect("script executes");
    assert_eq!(
        out.first().map(String::as_str),
        Some("sat"),
        "z3: sat (model xi = 9, validated); `unknown` is the missed interval refutation (the S3 NOCOL decline), `unsat` would be a fabricated refutation"
    );
}
