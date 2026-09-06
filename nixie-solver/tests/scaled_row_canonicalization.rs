//! Regression tests for large-constant linear rows (obligation fuzzer
//! finding 5: the scaled `gap` family).
//!
//! Every coefficient here is a multiple of 10⁹, matching the fuzzer's
//! `scale_log10` numeral stress.  Before row canonicalization
//! (`canonicalize_lin_form`), these rows entered the exact-rational tableau
//! raw: a couple of pivots multiply 10⁹-scale coefficients together, the
//! `i64` `Rational64` products overflow, the pivot is transactionally
//! refused, `resource_limit` trips, and the LP answers an honest `Unknown`
//! — where the LP question itself is trivial (a handful of variables with
//! small-integer structure once the common 10⁹ factor is divided out).
//!
//! The fix rescales every row by `lcm(denominators)/gcd(|numerators|)` at
//! the single choke point rows pass through, so a row asserted as
//! `3·10⁹·x + 6·10⁹·y = 6·10⁹` is interned as `3x + 6y = 6`.  The tests
//! pin, in order of scope:
//!
//! 1. the scaled LRA `gap` twin decides `sat` (its certificate is the
//!    rational half-integer solution),
//! 2. the scaled LIA twin decides `unsat` (integer-infeasible, LP-sat —
//!    the gap certificate),
//! 3. strict scaled inequalities (the δ-encoding path) keep their exact
//!    semantics under rescaling, both polarities,
//! 4. a formula and its uniformly rescaled copy (every constant ×3) agree,
//! 5. an integer gap whose rhs shares the coefficient gcd is *satisfiable*
//!    — canonicalization must not turn a solvable row into an unsolvable
//!    one (`2·10⁹·x = 4·10⁹` is `x = 2`, not a parity contradiction).

use nixie_solver::Context;

fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script)
        .expect("script should parse and run")
}

#[test]
fn scaled_gap_lra_twin_is_sat() {
    // Rationally satisfiable at x0 = x1 = x2 = 1/2:
    //   3e9·x0 + 6e9·x1 + 3e9·x2 = 6e9   (1.5 + 3 + 1.5)
    //   6e9·x0 - 3e9·x1         = 1.5e9  (3 - 1.5)
    // Before the fix: pivot overflow → Unknown.
    let output = run(r#"
        (set-logic QF_LRA)
        (declare-fun x0 () Real)
        (declare-fun x1 () Real)
        (declare-fun x2 () Real)
        (assert (>= x0 0.0))
        (assert (<= x0 1.0))
        (assert (>= x1 0.0))
        (assert (<= x1 1.0))
        (assert (>= x2 0.0))
        (assert (<= x2 1.0))
        (assert (= (+ (* 3000000000.0 x0) (* 6000000000.0 x1) (* 3000000000.0 x2)) 6000000000.0))
        (assert (= (+ (* 6000000000.0 x0) (* (- 3000000000.0) x1)) 1500000000.0))
        (check-sat)
    "#);
    assert_eq!(output, vec!["sat"]);
}

#[test]
fn scaled_gap_lia_twin_is_unsat() {
    // Integer-infeasible, rationally satisfiable (the gap certificate):
    //   2e9·x0 + 2e9·x1 = 3e9   →  2x0 + 2x1 = 3, parity contradiction.
    let output = run(r#"
        (set-logic QF_LIA)
        (declare-fun x0 () Int)
        (declare-fun x1 () Int)
        (assert (>= x0 0))
        (assert (<= x0 1000000000))
        (assert (>= x1 0))
        (assert (<= x1 1000000000))
        (assert (= (+ (* 2000000000 x0) (* 2000000000 x1)) 3000000000))
        (check-sat)
    "#);
    assert_eq!(output, vec!["unsat"]);
}

#[test]
fn scaled_lia_gap_with_divisible_rhs_is_sat() {
    // `2e9·x = 4e9` divides: x = 2.  Canonicalization must preserve the
    // solution set exactly — a rescaled row may never widen or narrow it.
    let output = run(r#"
        (set-logic QF_LIA)
        (declare-fun x () Int)
        (assert (>= x 0))
        (assert (<= x 1000000000))
        (assert (= (* 2000000000 x) 4000000000))
        (check-sat)
    "#);
    assert_eq!(output, vec!["sat"]);
}

#[test]
fn strict_scaled_inequality_unsat_side() {
    // x0 + 2·x1 < 1.5 with x0 = 1, x1 = 1/4: the boundary case 1.5 < 1.5
    // is false — strictness must survive the 2·10⁹ rescaling (the δ
    // encoding lives in ℚ[ε]; a positive row rescaling rescales δ
    // magnitudes, which the framework admits).
    let output = run(r#"
        (set-logic QF_LRA)
        (declare-fun x0 () Real)
        (declare-fun x1 () Real)
        (assert (= x0 1.0))
        (assert (= x1 0.25))
        (assert (< (+ (* 2000000000.0 x0) (* 4000000000.0 x1)) 3000000000.0))
        (check-sat)
    "#);
    assert_eq!(output, vec!["unsat"]);
}

#[test]
fn strict_scaled_inequality_sat_side() {
    // Same shape, strictly below the boundary: 1.4 < 1.5 holds.
    let output = run(r#"
        (set-logic QF_LRA)
        (declare-fun x0 () Real)
        (declare-fun x1 () Real)
        (assert (= x0 1.0))
        (assert (= x1 0.2))
        (assert (< (+ (* 2000000000.0 x0) (* 4000000000.0 x1)) 3000000000.0))
        (check-sat)
    "#);
    assert_eq!(output, vec!["sat"]);
}

#[test]
fn uniform_rescaling_of_the_whole_formula_preserves_the_verdict() {
    // The same system with the equality row's constants multiplied by 3:
    // identical normalized row, identical verdicts (both polarities).
    // (A positive rescaling of ONE row is exactly the transform
    // `canonicalize_lin_form` divides out; the variable bounds stay put.)
    let sat_base = r#"
        (set-logic QF_LRA)
        (declare-fun x0 () Real)
        (declare-fun x1 () Real)
        (assert (>= x0 0.0))
        (assert (<= x0 1.0))
        (assert (= (+ (* 1000000000.0 x0) (* 2000000000.0 x1)) 2500000000.0))
        (assert (< x1 1.5))
        (check-sat)
    "#;
    let sat_scaled = r#"
        (set-logic QF_LRA)
        (declare-fun x0 () Real)
        (declare-fun x1 () Real)
        (assert (>= x0 0.0))
        (assert (<= x0 1.0))
        (assert (= (+ (* 3000000000.0 x0) (* 6000000000.0 x1)) 7500000000.0))
        (assert (< x1 1.5))
        (check-sat)
    "#;
    // x0 + 2·x1 = 2.5 with 0 <= x0 <= 1 and x1 < 1.5: satisfiable
    // (x0 = 1, x1 = 0.75) in both encodings.
    assert_eq!(run(sat_base), vec!["sat"]);
    assert_eq!(run(sat_scaled), vec!["sat"]);

    let unsat_base = r#"
        (set-logic QF_LRA)
        (declare-fun x0 () Real)
        (declare-fun x1 () Real)
        (assert (>= x0 0.0))
        (assert (<= x0 1.0))
        (assert (= (+ (* 1000000000.0 x0) (* 2000000000.0 x1)) 2500000000.0))
        (assert (< x1 0.5))
        (check-sat)
    "#;
    let unsat_scaled = r#"
        (set-logic QF_LRA)
        (declare-fun x0 () Real)
        (declare-fun x1 () Real)
        (assert (>= x0 0.0))
        (assert (<= x0 1.0))
        (assert (= (+ (* 3000000000.0 x0) (* 6000000000.0 x1)) 7500000000.0))
        (assert (< x1 0.5))
        (check-sat)
    "#;
    // x0 + 2·x1 = 2.5 forces x1 >= 0.75; x1 < 0.5 contradicts.
    assert_eq!(run(unsat_base), vec!["unsat"]);
    assert_eq!(run(unsat_scaled), vec!["unsat"]);
}

#[test]
fn scaled_lra_twin_many_rows_still_decides() {
    // Eight equality rows over eleven [0,1] variables, the fuzzer's large
    // `gap` LRA shape in miniature: before the fix this exact shape burned
    // the pivot budget on overflow and answered Unknown.
    let mut script = String::from(
        "(set-logic QF_LRA)\n(declare-fun x0 () Real)\n(declare-fun x1 () Real)\n\
         (declare-fun x2 () Real)\n(declare-fun x3 () Real)\n(declare-fun x4 () Real)\n\
         (declare-fun x5 () Real)\n(declare-fun x6 () Real)\n(declare-fun x7 () Real)\n\
         (declare-fun x8 () Real)\n(declare-fun x9 () Real)\n(declare-fun x10 () Real)\n",
    );
    for i in 0..11 {
        script.push_str(&format!("(assert (>= x{i} 0.0))\n(assert (<= x{i} 1.0))\n"));
    }
    // Rows satisfied exactly by x_i = 1/2 (coefficients in units of 10⁹).
    let rows: [[i64; 11]; 8] = [
        [-6, -12, -8, 0, 4, -6, -4, -12, -10, 2, -10],
        [-4, 6, 2, 6, -6, 0, -4, 4, -4, 0, 0],
        [-4, -6, -6, 0, 4, 6, 2, 2, 4, -2, -2],
        [-2, 6, 6, -6, 2, 0, -4, -6, 0, -6, 0],
        [6, -6, 0, 4, 0, -4, -6, 6, 6, 2, 2],
        [2, 6, -2, -2, 0, -4, 2, -4, -6, 2, -6],
        [6, -2, -4, -6, -4, 6, -4, -4, -2, -2, 2],
        [6, -4, 2, 4, 0, -2, 0, 0, 0, 4, -4],
    ];
    // Row sums at x = 1/2 (in units of 10⁹), each row's rhs:
    let rhs: [i64; 8] = [-31, 0, -1, -5, 5, -6, -7, 3];
    for (r, c) in rows.iter().zip(rhs.iter()) {
        script.push_str("(assert (= (+");
        for (i, a) in r.iter().enumerate() {
            if *a != 0 {
                script.push_str(&format!(" (* {}.0 x{})", *a * 1_000_000_000, i));
            }
        }
        script.push_str(&format!(") {}.0))\n", *c * 1_000_000_000));
    }
    script.push_str("(check-sat)\n");
    assert_eq!(run(&script), vec!["sat"]);
}
