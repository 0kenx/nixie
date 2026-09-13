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
use nixie_core::ast::TermKind;
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

/// The residual accumulator-overflow class: nested `Sub` whose *leaves* fold
/// but whose constant sum (`i64::MAX + 1`) only assembles inside the linear
/// parse.  The walk must fail honestly (gate to `Unknown`), never panic
/// (debug) and never wrap (release).  A valid claim's negation must never
/// be `Sat`.
#[test]
fn nested_constant_overflow_is_gated_never_wrapped() {
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
    assert_ne!(r, SolverResult::Sat, "a valid claim must never be Sat");
}

// ======== `/` vs `div`: SMT-LIB division semantics ========

/// `/` is REAL division: `(/ 7 2)` is `7/2`, not Euclidean `3`.  Routing `/`
/// through the integer constructor answered `(/ 7 2) = 3` with `sat` and
/// `(/ 7 2) > 3` with `unsat` — both wrong.
#[test]
fn real_slash_is_not_integer_division() {
    let mut tm = TermManager::new();
    let seven = tm.mk_int(7);
    let two = tm.mk_int(2);
    let q = tm.mk_rdiv(seven, two);
    // the node is Real-sorted and folds to 7/2
    match &tm.get(q).expect("term").kind {
        TermKind::RealConst(r) => assert_eq!(*r, num_rational::Rational64::new(7, 2)),
        other => panic!("(/ 7 2) must fold to RealConst(7/2), got {other:?}"),
    }
    // ...and comparisons over it are exact
    let three = tm.mk_int(3);
    let eq_three = tm.mk_eq(q, three); // 3.5 = 3 is false
    assert!(matches!(
        &tm.get(eq_three).expect("term").kind,
        TermKind::False
    ));
    let gt_three = tm.mk_gt(q, three); // 3.5 > 3 is true
    assert!(matches!(
        &tm.get(gt_three).expect("term").kind,
        TermKind::True
    ));
}

/// `div` stays Euclidean integer division on the same literals.
#[test]
fn int_div_stays_euclidean() {
    let mut tm = TermManager::new();
    let seven = tm.mk_int(7);
    let two = tm.mk_int(2);
    let q = tm.mk_div(seven, two);
    match &tm.get(q).expect("term").kind {
        TermKind::IntConst(n) => assert_eq!(*n, num_bigint::BigInt::from(3)),
        other => panic!("(div 7 2) must fold to 3, got {other:?}"),
    }
}

/// Real division by a numeral constant linearizes (`(/ x 3.0)` ≡
/// `(* x (1/3))`) and is decidable.
#[test]
fn real_division_by_constant_is_decidable() {
    use nixie_solver::Context;
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(declare-const x Real)(assert (= (/ x 3.0) 2.0))(check-sat)(get-value (x))",
        )
        .expect("script");
    assert!(out[0].contains("sat"), "{}", out[0]);
    // the printer may render the rational 6 as `6`, `6.0` or `(/ 6.0 1.0)`
    assert!(
        out[1].contains("x 6.0")
            || out[1].contains("x (/ 6.0")
            || out[1].trim_end_matches(')').contains("x 6"),
        "{}",
        out[1]
    );
}

/// Mixed `Int`/`Real` arithmetic gets the REAL sort whichever way the
/// operands are ordered (`Int` is a subsort of `Real`): `(+ xi yr)` used to
/// be `Int`-sorted when written operand-first, feeding integer-only
/// reasoning a row whose value can be fractional.
#[test]
fn mixed_int_real_add_is_real_sorted_either_order() {
    let mut tm = TermManager::new();
    let xi = tm.mk_var("xi", tm.sorts.int_sort);
    let yr = tm.mk_var("yr", tm.sorts.real_sort);
    let half = tm.mk_real(num_rational::Rational64::new(1, 2));
    let a = tm.mk_add([xi, yr]);
    let b = tm.mk_add([yr, xi]);
    let c = tm.mk_add([xi, half]);
    for t in [a, b, c] {
        let node = tm.get(t).expect("term");
        assert_eq!(
            node.sort, tm.sorts.real_sort,
            "mixed add must be Real-sorted"
        );
    }
    // and a mixed sum with a fractional offset stays satisfiable
    let mut s = nixie_solver::Solver::new();
    let xi2 = tm.mk_var("xi", tm.sorts.int_sort);
    let half2 = tm.mk_real(num_rational::Rational64::new(1, 2));
    let sum = tm.mk_add([xi2, half2]);
    let claim = tm.mk_eq(sum, half2);
    s.assert(claim, &mut tm);
    assert_eq!(s.check(&mut tm), nixie_solver::SolverResult::Sat); // xi = 0
}

/// Ill-sorted `mod`/`div` (a Real operand) is a parse error — the
/// standard-mandated answer.  (z3 silently coerces via `to_int`, a
/// nonstandard extension; nixie rejects, exactly as it rejects mixed-width
/// bit-vector operands.)
#[test]
fn ill_sorted_mod_and_div_are_parse_errors() {
    use nixie_solver::Context;
    for bad in [
        "(declare-const x Real)(assert (= (mod x 3) 1))",
        "(assert (= (mod 1.5 3) 1))",
        "(declare-const x Real)(assert (= (div x 2) 1))",
    ] {
        let mut ctx = Context::new();
        let script = format!("{bad}(check-sat)");
        // a parse error aborts the script (no verdict is produced at all)
        let err = ctx
            .execute_script(&script)
            .expect_err("ill-sorted mod/div must be rejected at parse time");
        let msg = format!("{err}");
        assert!(msg.contains("Int"), "unexpected error: {msg}");
    }
}
