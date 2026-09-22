//! Transcendental theory (δ-ICP) integration tests.
//!
//! Every verdict here is a soundness contract (see `docs/TRANS.md`):
//!
//! * `unsat` answers must be TRUE refutations — δ-unsat implies unsat;
//! * `delta-sat` answers must come with a witness whose published values
//!   were re-verified after rounding (the engine checks exactly what it
//!   prints), and that witness must make every assertion's arithmetic
//!   δ-tolerable — several tests re-check the printed values against the
//!   known roots (ln 2, π, tan 1, …);
//! * `unknown` is the required answer for the fragments the engine
//!   declines (UF inside arithmetic, quantifiers, closed logics).

use nixie_solver::Context;

fn run_all(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script).expect("script executes")
}

fn run_last(script: &str) -> String {
    run_all(script).last().cloned().unwrap_or_default()
}

/// The `check-sat` verdict line (first output of every script here).
fn run_sat(script: &str) -> String {
    run_all(script).first().cloned().unwrap_or_default()
}

/// Extract the value of `x` from a `(get-value (x))` answer, as f64.
fn x_value(script: &str) -> f64 {
    let r = run_last(script);
    // Answer shapes: ((x (/ n d))) or ((x 2.0)).
    if let Some(i) = r.find("(/ ") {
        let start = i + 3;
        let end = r[start..]
            .find([')', ' '])
            .map(|j| start + j)
            .unwrap_or(r.len());
        let numer: f64 = r[start..end].trim().parse().unwrap_or(f64::NAN);
        let dstart = end;
        let dend = r[dstart..].find(')').map(|j| dstart + j).unwrap_or(r.len());
        let denom: f64 = r[dstart..dend].trim().parse().unwrap_or(f64::NAN);
        return numer / denom;
    }
    let inner = r.trim_matches(|c| c == '(' || c == ')');
    inner
        .rsplit(' ')
        .next()
        .unwrap_or("")
        .trim()
        .parse()
        .unwrap_or(f64::NAN)
}

// ======== δ-satisfiable goals (the answer must be delta-sat) ========

#[test]
fn exp_equals_two_is_delta_sat_at_ln2() {
    let script = r#"(set-logic QF_NRT)
        (declare-const x Real)
        (assert (= (exp x) 2.0))
        (check-sat)
        (get-value (x))"#;
    assert_eq!(run_sat(script), "delta-sat");
    // The witness must be ln 2 within δ-tolerance (0.001).
    let v = x_value(script);
    assert!(
        (v - core::f64::consts::LN_2).abs() < 5e-3,
        "witness {v} not near ln 2"
    );
}

#[test]
fn sin_zero_on_pi_is_delta_sat() {
    let script = r#"(set-logic QF_NRT)
        (declare-const x Real)
        (assert (= (sin x) 0.0))
        (assert (and (>= x 3.0) (<= x 3.5)))
        (check-sat)
        (get-value (x))"#;
    assert_eq!(run_sat(script), "delta-sat");
    let v = x_value(script);
    assert!(
        (v - core::f64::consts::PI).abs() < 5e-3,
        "witness {v} not near π"
    );
}

#[test]
fn sqrt_four_is_delta_sat() {
    let script = r#"(set-logic QF_NRT)
        (declare-const x Real)
        (assert (= (sqrt x) 2.0))
        (check-sat)
        (get-value (x))"#;
    assert_eq!(run_sat(script), "delta-sat");
    let v = x_value(script);
    assert!((v - 4.0).abs() < 5e-3, "witness {v} not near 4");
}

#[test]
fn atan_lower_bound_is_delta_sat() {
    // atan(x) ≥ 1 has solutions x ≥ tan(1) ≈ 1.5574.
    let script = r#"(set-logic QF_NRT)
        (declare-const x Real)
        (assert (>= (atan x) 1.0))
        (check-sat)
        (get-value (x))"#;
    assert_eq!(run_sat(script), "delta-sat");
    let v = x_value(script);
    assert!(v > 1.5, "witness {v} not above tan(1)");
}

#[test]
fn log_exp_roundtrip_is_delta_sat() {
    // x = exp(log(x)) for x > 0: any x in (0, ∞) works.
    let script = r#"(set-logic QF_NRT)
        (declare-const x Real)
        (assert (>= x 0.5))
        (assert (<= x 2.0))
        (assert (= (exp (log x)) x))
        (check-sat)"#;
    assert_eq!(run_sat(script), "delta-sat");
}

#[test]
fn disjunction_picks_the_far_branch() {
    // (exp x = 2 ∨ exp x = 8) ∧ x ≥ 1.5: only ln 8 ≈ 2.079 qualifies.
    let script = r#"(set-logic QF_NRT)
        (declare-const x Real)
        (assert (or (= (exp x) 2.0) (= (exp x) 8.0)))
        (assert (>= x 1.5))
        (check-sat)
        (get-value (x))"#;
    assert_eq!(run_sat(script), "delta-sat");
    let v = x_value(script);
    assert!((v - 8.0f64.ln()).abs() < 5e-3, "witness {v} not near ln 8");
}

#[test]
fn numeric_ite_resolves_per_assignment() {
    // x = ite(b, 4, 9) ∧ sqrt(x) = 2: the b=true branch satisfies.
    let script = r#"(set-logic QF_NRT)
        (declare-const x Real)
        (declare-const b Bool)
        (assert (= x (ite b 4.0 9.0)))
        (assert (= (sqrt x) 2.0))
        (check-sat)"#;
    assert_eq!(run_sat(script), "delta-sat");
}

#[test]
fn cosine_zero_crossing_is_delta_sat() {
    // cos(x) = 0 ∧ x ∈ [1, 2]: root at π/2 ≈ 1.5708.
    let script = r#"(set-logic QF_NRT)
        (declare-const x Real)
        (assert (= (cos x) 0.0))
        (assert (and (>= x 1.0) (<= x 2.0)))
        (check-sat)
        (get-value (x))"#;
    assert_eq!(run_sat(script), "delta-sat");
    let v = x_value(script);
    assert!(
        (v - core::f64::consts::FRAC_PI_2).abs() < 5e-3,
        "witness {v} not near π/2"
    );
}

// ======== unsatisfiable goals (unsat must be a TRUE refutation) ========

#[test]
fn exp_upper_bounded_below_one_with_positive_x_is_unsat() {
    let r = run_last(
        r#"(set-logic QF_NRT)
        (declare-const x Real)
        (assert (>= x 1.0))
        (assert (<= (exp x) 1.0))
        (check-sat)"#,
    );
    assert_eq!(r, "unsat", "exp(x) ≥ e > 1 + δ for x ≥ 1");
}

#[test]
fn log_ge_one_with_x_le_two_is_unsat() {
    let r = run_last(
        r#"(set-logic QF_NRT)
        (declare-const x Real)
        (assert (>= (log x) 1.0))
        (assert (<= x 2.0))
        (check-sat)"#,
    );
    assert_eq!(r, "unsat", "log(x) ≥ 1 forces x ≥ e ≈ 2.718 > 2 + δ");
}

#[test]
fn sin_strictly_between_branches_is_unsat() {
    // sin(x) = 0 has no root in [3.2, 3.3]: π ≈ 3.14159 is δ-far below.
    let r = run_last(
        r#"(set-logic QF_NRT)
        (declare-const x Real)
        (assert (= (sin x) 0.0))
        (assert (and (>= x 3.2) (<= x 3.3)))
        (check-sat)"#,
    );
    assert_eq!(r, "unsat", "no k·π within δ of [3.2, 3.3]");
}

#[test]
fn both_disjuncts_refuted_is_unsat() {
    // (exp x = 2 ∨ exp x = 3) ∧ x ≥ 1.5: ln 2 ≈ 0.69, ln 3 ≈ 1.10 both
    // below 1.5 − δ.
    let r = run_last(
        r#"(set-logic QF_NRT)
        (declare-const x Real)
        (assert (or (= (exp x) 2.0) (= (exp x) 3.0)))
        (assert (>= x 1.5))
        (check-sat)"#,
    );
    assert_eq!(r, "unsat");
}

#[test]
fn sqrt_negative_lower_bound_is_unsat() {
    // sqrt(x) ≥ 3 forces x ≥ 9; x ≤ 8 contradicts with δ-margin.
    let r = run_last(
        r#"(set-logic QF_NRT)
        (declare-const x Real)
        (assert (>= (sqrt x) 3.0))
        (assert (<= x 8.0))
        (check-sat)"#,
    );
    assert_eq!(r, "unsat");
}

#[test]
fn trig_identity_contradiction_bounded_is_unsat() {
    // sin²(x) + cos²(x) = 0 is impossible (it is 1 everywhere), with a
    // δ-margin of 1 — over a BOUNDED x, propagation + bisection covers
    // every box and refutes.
    let r = run_sat(
        r#"(set-logic QF_NRT)
        (declare-const x Real)
        (assert (= (+ (* (sin x) (sin x)) (* (cos x) (cos x))) 0.0))
        (assert (and (>= x 0.0) (<= x 6.0)))
        (check-sat)"#,
    );
    assert_eq!(r, "unsat", "sin² + cos² = 1 everywhere on [0,6]");
}

#[test]
fn trig_identity_contradiction_unbounded_is_unknown() {
    // The same identity over ALL of ℝ cannot be refuted by bisection (a
    // periodic function over an unbounded ray never runs out of boxes) —
    // the honest verdict is `unknown`, never a guess.  dReal shares this
    // limitation; see docs/TRANS.md.
    let r = run_sat(
        r#"(set-logic QF_NRT)
        (declare-const x Real)
        (assert (= (+ (* (sin x) (sin x)) (* (cos x) (cos x))) 0.0))
        (check-sat)"#,
    );
    assert_eq!(r, "unknown", "unbounded periodic identity stays unknown");
}

// ======== honesty: declined fragments answer unknown, never guess ========

#[test]
fn uninterpreted_function_in_trans_arithmetic_is_unknown() {
    // UF congruence is EUF semantics the ICP fragment does not carry: with
    // x = y the congruence f(x) = f(y) makes the goal unsat, but treating
    // f(x), f(y) as free arithmetic would δ-sat it.  The dispatcher must
    // decline (the goal contains trans terms via the exp constraints).
    let r = run_sat(
        r#"(set-logic QF_NRT)
        (declare-fun f (Real) Real)
        (declare-const x Real)
        (declare-const y Real)
        (assert (= x y))
        (assert (< (exp (f x)) 1.0))
        (assert (> (exp (f y)) 2.0))
        (check-sat)"#,
    );
    assert_eq!(r, "unknown", "UF inside trans arithmetic must be declined");
}

#[test]
fn quantifier_is_declined_by_the_logic_contract() {
    // QF_NRT declares a quantifier-free fragment: the contract layer
    // rejects the script outright (an error is stricter and better than a
    // verdict-line `unknown`).
    let mut ctx = Context::new();
    let out = ctx.execute_script(
        r#"(set-logic QF_NRT)
        (declare-const x Real)
        (assert (exists ((y Real)) (= (exp y) x)))
        (assert (<= x 0.0))
        (check-sat)"#,
    );
    assert!(
        out.is_err(),
        "the quantifier must violate the QF contract, got {out:?}"
    );
}

#[test]
fn closed_logic_keeps_contract() {
    // QF_LRA does not contain transcendentals: the contract layer rejects
    // the script outright — never a linearized guess.
    let mut ctx = Context::new();
    let out = ctx.execute_script(
        r#"(set-logic QF_LRA)
        (declare-const x Real)
        (assert (= (exp x) 2.0))
        (check-sat)"#,
    );
    assert!(
        out.is_err(),
        "trans atoms under QF_LRA must violate the contract, got {out:?}"
    );
}

#[test]
fn pure_polynomial_goals_still_route_to_nlsat() {
    // No trans term: the ordinary engines own the goal (regression guard
    // for the dispatcher's gate).
    let r = run_last(
        r#"(set-logic QF_NRA)
        (declare-const x Real)
        (assert (= (* x x) 2.0))
        (assert (> x 0.0))
        (check-sat)"#,
    );
    assert_eq!(r, "sat", "NLSAT handles the polynomial goal exactly");
}

// ======== δ option plumbing ========

#[test]
fn delta_option_changes_the_tolerance() {
    // With δ = 0.1, sin(x) = 0 accepts x within ~0.1 of any k·π: x = 3.25
    // (≈ π + 0.108 ≈ δ-close) becomes admissible where δ = 0.001 refused.
    let wide = run_sat(
        r#"(set-logic QF_NRT)
        (set-option :delta 0.15)
        (declare-const x Real)
        (assert (= (sin x) 0.0))
        (assert (and (>= x 3.2) (<= x 3.3)))
        (check-sat)"#,
    );
    assert_eq!(wide, "delta-sat", "δ=0.15 admits the near-root box");
}

#[test]
fn delta_option_reaches_the_engine_config() {
    let mut ctx = Context::new();
    ctx.execute_script(
        r#"(set-logic QF_NRT)
        (set-option :delta 0.15)"#,
    )
    .expect("script executes");
    assert_eq!(
        ctx.solver_config().trans_delta_nanos,
        150_000_000,
        "the delta option must land in the config"
    );
}
