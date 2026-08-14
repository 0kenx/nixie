//! End-to-end regression tests pinning the SMT-LIB `Ints` theory's Euclidean
//! `div`/`mod` convention through the *linear* (CDCL(T)/simplex) path --
//! `QF_LIA`, never `QF_NIA`, so `dispatch_nia_constraints`'s nonlinear-only
//! dispatch (see `oxiz-theories/tests/pr27_nia_divmod.rs`, which covers
//! *that* path instead) never engages and every case here is decided by
//! `oxiz-solver`'s own `arith_axioms` ground-lemma encoder plus the linear
//! arithmetic tableau.
//!
//! Every script below declares `(set-logic QF_LIA)` explicitly. This is not
//! decorative: `arith_axioms::instantiate_arith_axioms` only asserts the
//! Euclidean defining axioms in *integer mode*
//! (`self.arith.is_integer()`) – real mode leaves `div`/`mod` deliberately
//! undefined, per that module's own doc comment, because "the quotient
//! being an integer" is what the axioms rest on. Integer mode is decided
//! from the declared logic, not merely from every operand happening to be
//! `Int`-sorted, so a script that never calls `set-logic` at all answers
//! `unknown` for a `div`/`mod` query regardless of declared sorts – a
//! pre-existing, logic-string-driven gate this file does not change or
//! attempt to relax, and works around the documented way (declaring the
//! logic, exactly as a conformant SMT-LIB2 script must).
//!
//! ## The convention being pinned
//!
//! For a nonzero divisor `n`, `(div m n)` and `(mod m n)` are the unique
//! `q`, `r` satisfying `m = n·q + r` with `0 ≤ r < |n|` – the remainder is
//! never negative, regardless of either operand's sign. Hand-computed
//! expectations used below:
//!
//! * `7 = 2·3 + 1`             → `(div 7 2) = 3`,        `(mod 7 2) = 1`
//! * `7 = (-2)·(-3) + 1`       → `(div 7 (- 2)) = -3`,   `(mod 7 (- 2)) = 1`
//! * `-7 = 2·(-4) + 1`         → `(div (- 7) 2) = -4`,   `(mod (- 7) 2) = 1`
//! * `-7 = (-2)·4 + 1`         → `(div (- 7) (- 2)) = 4`, `(mod (- 7) (- 2)) = 1`
//! * `8 = 2·4 + 0`             → boundary `r = 0`:        `(mod 8 2) = 0`
//! * `-1 = 7·(-1) + 6`         → boundary `r = |n|-1`:    `(mod (- 1) 7) = 6`
//!
//! Negative *values* the printer emits are bare signed numerals (`-3`), not
//! the `(- 3)` s-expression form used for a negative *literal in source
//! text* -- `get-value`'s left-hand column echoes the query exactly as
//! written (so a source `(- 2)` stays `(- 2)`) while its right-hand column
//! prints a freshly built `IntConst` value, which is a different code path
//! with a different (pre-existing, unrelated to this change) convention.
//!
//! ## What this also exercises
//!
//! `get-value` on a `div`/`mod` expression used to echo the term back
//! unevaluated instead of folding it (`Model::eval` in
//! `oxiz-solver/src/solver/types.rs` had no case for `TermKind::Div`/`Mod`
//! at all, so the compound term fell through its catch-all "already
//! consulted the model" arm without even substituting the variable's model
//! value into it) -- reproduced on a bare `(get-value ((div x 2)))` query
//! with *no* `div`/`mod` term anywhere else in the script, so it is a
//! pre-existing gap in `get-value`'s own evaluator, independent of
//! `arith_axioms`'s (already-correct) constraint semantics. Every case here
//! that checks `get-value` output pins the fix for that gap too.

use oxiz_solver::Context;

/// Run `script` through a fresh [`Context`], returning its output lines.
fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script)
        .expect("script should parse and run")
}

/// Positive dividend, positive divisor: `(div 7 2)=3`, `(mod 7 2)=1`.
#[test]
fn test_pr27_divmod_positive_dividend_positive_divisor() {
    let output = run(r#"
        (set-logic QF_LIA)
        (check-sat)
        (get-value ((div 7 2) (mod 7 2)))
    "#);
    assert_eq!(output[0], "sat");
    assert!(output[1].contains("(div 7 2) 3"), "{}", output[1]);
    assert!(output[1].contains("(mod 7 2) 1"), "{}", output[1]);
}

/// Positive dividend, negative divisor: `(div 7 (- 2))=-3`, `(mod 7 (- 2))=1`.
/// The remainder stays non-negative even though the divisor is negative.
#[test]
fn test_pr27_divmod_positive_dividend_negative_divisor() {
    let output = run(r#"
        (set-logic QF_LIA)
        (check-sat)
        (get-value ((div 7 (- 2)) (mod 7 (- 2))))
    "#);
    assert_eq!(output[0], "sat");
    assert!(output[1].contains("(div 7 (- 2)) -3"), "{}", output[1]);
    assert!(output[1].contains("(mod 7 (- 2)) 1"), "{}", output[1]);
}

/// Negative dividend, positive divisor: `(div (- 7) 2)=-4`, `(mod (- 7) 2)=1`.
/// Rust's truncating `/`/`%` would give `-3`/`-1`; the Euclidean convention
/// rounds the quotient *down* (away from truncation-toward-zero) so the
/// remainder stays non-negative.
#[test]
fn test_pr27_divmod_negative_dividend_positive_divisor() {
    let output = run(r#"
        (set-logic QF_LIA)
        (check-sat)
        (get-value ((div (- 7) 2) (mod (- 7) 2)))
    "#);
    assert_eq!(output[0], "sat");
    assert!(output[1].contains("(div (- 7) 2) -4"), "{}", output[1]);
    assert!(output[1].contains("(mod (- 7) 2) 1"), "{}", output[1]);
}

/// Negative dividend, negative divisor: `(div (- 7) (- 2))=4`,
/// `(mod (- 7) (- 2))=1`.
#[test]
fn test_pr27_divmod_negative_dividend_negative_divisor() {
    let output = run(r#"
        (set-logic QF_LIA)
        (check-sat)
        (get-value ((div (- 7) (- 2)) (mod (- 7) (- 2))))
    "#);
    assert_eq!(output[0], "sat");
    assert!(output[1].contains("(div (- 7) (- 2)) 4"), "{}", output[1]);
    assert!(output[1].contains("(mod (- 7) (- 2)) 1"), "{}", output[1]);
}

/// Boundary: exact division, remainder `0`.
#[test]
fn test_pr27_divmod_boundary_remainder_zero() {
    let output = run(r#"
        (set-logic QF_LIA)
        (check-sat)
        (get-value ((div 8 2) (mod 8 2)))
    "#);
    assert_eq!(output[0], "sat");
    assert!(output[1].contains("(div 8 2) 4"), "{}", output[1]);
    assert!(output[1].contains("(mod 8 2) 0"), "{}", output[1]);
}

/// Boundary: remainder at its maximum, `|n|-1`. `-1 = 7*(-1) + 6`.
#[test]
fn test_pr27_divmod_boundary_remainder_at_upper_bound() {
    let output = run(r#"
        (set-logic QF_LIA)
        (check-sat)
        (get-value ((div (- 1) 7) (mod (- 1) 7)))
    "#);
    assert_eq!(output[0], "sat");
    assert!(output[1].contains("(div (- 1) 7) -1"), "{}", output[1]);
    assert!(output[1].contains("(mod (- 1) 7) 6"), "{}", output[1]);
}

/// A variable dividend, pinned indirectly: `x = -7` forces
/// `(div x 2) = -4`, `(mod x 2) = 1` through the *ground-lemma* Euclidean
/// axioms (`arith_axioms.rs`), not a literal constant fold -- this is the
/// shape that actually exercises `instantiate_arith_axioms` end to end, as
/// opposed to the bare-literal cases above (which a constant-folding pass
/// alone could satisfy without the axioms ever firing).
#[test]
fn test_pr27_divmod_variable_dividend_forces_unique_value() {
    let output = run(r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x (- 7)))
        (check-sat)
        (get-value ((div x 2) (mod x 2)))
    "#);
    assert_eq!(output[0], "sat");
    assert!(output[1].contains("(div x 2) -4"), "{}", output[1]);
    assert!(output[1].contains("(mod x 2) 1"), "{}", output[1]);
}

/// A variable divisor is folded once *its own* value is pinned too:
/// `x = 10`, `n = -3`. Euclidean semantics force `10 = (-3)*(-3) + 1`, so
/// `(div x n) = -3`, `(mod x n) = 1`.
#[test]
fn test_pr27_divmod_variable_divisor() {
    let output = run(r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const n Int)
        (assert (= x 10))
        (assert (= n (- 3)))
        (check-sat)
        (get-value ((div x n) (mod x n)))
    "#);
    assert_eq!(output[0], "sat");
    assert!(output[1].contains("(div x n) -3"), "{}", output[1]);
    assert!(output[1].contains("(mod x n) 1"), "{}", output[1]);
}

/// The Euclidean identity is a real constraint, not a decoration: asserting
/// a `mod` result outside `[0, n)` must be `unsat`. `mod` is always in
/// `[0, 5)` for divisor `5`; forcing it to `5` itself (out of range) leaves
/// no satisfying dividend.
#[test]
fn test_pr27_divmod_remainder_out_of_range_is_unsat() {
    let output = run(r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= (mod x 5) 5))
        (check-sat)
    "#);
    assert_eq!(output[0], "unsat", "mod result is always in [0, 5)");
}

/// Same shape with a negative divisor: `(mod x (- 5))` is always in `[0, 5)`
/// too (magnitude, not sign, of the divisor bounds it); forcing it to a
/// negative value is UNSAT.
#[test]
fn test_pr27_divmod_negative_divisor_remainder_cannot_be_negative_is_unsat() {
    let output = run(r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= (mod x (- 5)) (- 1)))
        (check-sat)
    "#);
    assert_eq!(
        output[0], "unsat",
        "mod result is never negative, even with a negative divisor"
    );
}

/// Two variables pinned by their Euclidean relationship: `q = (div x 5)`,
/// `r = (mod x 5)`, `x = 23` forces `q=4, r=3` (`23 = 5*4+3`); asserting a
/// *wrong* pair (`q=5, r=3`, which would need `x=28`) must be `unsat`.
#[test]
fn test_pr27_divmod_wrong_quotient_remainder_pair_is_unsat() {
    let output = run(r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x 23))
        (assert (= (div x 5) 5))
        (assert (= (mod x 5) 3))
        (check-sat)
    "#);
    assert_eq!(
        output[0], "unsat",
        "23 = 5*4+3, not 5*5+3; the wrong quotient must be rejected"
    );
}

/// A *folded* (not bare-literal) divisor expression inside the *assertion*
/// itself: `(- (* 2 3) 1)` folds to `5`. `arith_axioms::int_constant` (this
/// path) must recognize that to instantiate the Euclidean axioms at all --
/// left symbolic, `(mod x (- (* 2 3) 1))` would just be a free variable and
/// every `x` in `[0,5)` would satisfy the script trivially rather than only
/// `x=3`. `oxiz-theories`' independent `resolve_int_divisor` (the QF_NIA
/// dispatch path, see
/// `oxiz-theories/tests/pr27_nia_divmod.rs::test_pr27_nia_divmod_folded_divisor_expression_is_sat`,
/// which folds the identical expression shape in an assertion the same way)
/// folds exactly the same `IntConst`/`Neg`/`Sub`/`Add`/`Mul` shapes,
/// checked `i64`-wise, so the two encoders cannot disagree on what this
/// divisor is. (The query term for `get-value` here is a bare variable, not
/// the folded expression itself, since `get-value`'s own evaluator folding
/// a *compound* divisor sub-expression *inside a query term* is a separate,
/// narrower concern from whether the axiom instantiator recognized it while
/// solving -- this test is about the latter.)
#[test]
fn test_pr27_divmod_folded_divisor_expression_in_assertion_is_sat() {
    let output = run(r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 0))
        (assert (< x 5))
        (assert (= (mod x (- (* 2 3) 1)) 3))
        (check-sat)
        (get-value (x))
    "#);
    assert_eq!(
        output[0], "sat",
        "divisor (2*3)-1 folds to 5; x=3 is the unique value in [0,5) with x mod 5=3"
    );
    assert!(output[1].contains("(x 3)"), "{}", output[1]);
}

/// `div`/`mod` by zero are uninterpreted per SMT-LIB, not total: this must
/// not crash and must not be treated as forcing a specific numeric value.
/// The one hard requirement is congruence -- two occurrences with the same
/// (zero-divisor) dividend must agree, checked directly rather than via
/// `get-value` (which is honestly allowed to leave an uninterpreted value
/// symbolic).
#[test]
fn test_pr27_divmod_zero_divisor_congruence_holds() {
    let output = run(r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= x y))
        (assert (not (= (mod x 0) (mod y 0))))
        (check-sat)
    "#);
    assert_eq!(
        output[0], "unsat",
        "mod-by-zero is a function of its dividend even though its value is unspecified"
    );
}
