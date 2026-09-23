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
fn uninterpreted_function_in_trans_arithmetic_is_decided() {
    // Ground UF over the reals is Ackermannized before the Boolean
    // abstraction: each application becomes a fresh variable and the
    // congruence `(x = y) ⇒ (f x = f y)` joins the skeleton as a clause.
    // With x = y asserted, both exp atoms read the SAME value — one below
    // 1, one above 2 — so every assignment is refuted: unsat, the EUF
    // answer (the pre-Ackermann engine honestly declined this to
    // `unknown`; the declined behavior is pinned below for quantifier-
    // tainted applications, which must NOT be Ackermannized).
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
    assert_eq!(r, "unsat", "ground UF congruence must refute, got {r}");
}

#[test]
fn ground_uf_trans_goal_can_be_delta_sat() {
    // The satisfiable side of Ackermannized UF: x = y forces f(x) = f(y),
    // and f(x) = ln 2 is expressible through exp.  δ-weakening makes the
    // 0.693-approximation tolerable (|0.693 − ln 2| ≈ 0.00015 < δ).
    let r = run_sat(
        r#"(set-logic QF_NRT)
        (declare-fun f (Real) Real)
        (declare-const x Real)
        (declare-const y Real)
        (declare-const t Real)
        (assert (>= x 0.0))
        (assert (<= x 1.0))
        (assert (= x y))
        (assert (= (exp (f x)) 2.0))
        (assert (= (f y) 0.693))
        (assert (= (sin t) 0.5))
        (assert (>= t 0.0))
        (assert (<= t 3.15))
        (check-sat)"#,
    );
    assert_eq!(r, "delta-sat", "Ackermannized δ-witness expected, got {r}");
}

#[test]
fn ground_uf_congruence_unsat_tighter_than_delta() {
    // The same shape tightened past δ: f(y) = 0.68 vs f(x) = ln 2 — the
    // δ-windows (0.68 ± 0.00168 and ln2 ± 0.0015 ⇒ [0.67832, 0.68168] vs
    // [0.69158, 0.69459]) are disjoint, so congruence refutes.
    let r = run_sat(
        r#"(set-logic QF_NRT)
        (declare-fun f (Real) Real)
        (declare-const x Real)
        (declare-const y Real)
        (assert (= x y))
        (assert (= (exp (f x)) 2.0))
        (assert (= (f y) 0.68))
        (check-sat)"#,
    );
    assert_eq!(
        r, "unsat",
        "congruence + δ-separated values refute, got {r}"
    );
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

// ======== distinct over the reals: pairwise negated equalities ========

#[test]
fn distinct_from_the_sin_root_refutes() {
    // x is pinned to π (sin x = 0 on [3, 4]) and required distinct from a
    // rational 3.14159 whose δ-window (±0.001·(1+3.14159) ≈ ±0.0041)
    // swallows every δ-root of sin x = 0 (π ± ~0.001): the negated
    // equality's box lies wholly inside the window, so the disequality
    // conflict fires — unsat.
    let r = run_sat(
        r#"(set-logic QF_NRT)
        (declare-const x Real)
        (assert (= (sin x) 0.0))
        (assert (>= x 3.0))
        (assert (<= x 4.0))
        (assert (distinct x 3.14159))
        (check-sat)"#,
    );
    assert_eq!(r, "unsat", "distinct-from-the-only-root refutes, got {r}");
}

#[test]
fn distinct_from_a_far_point_is_delta_sat() {
    // Same, but distinct from 2.0: π is ~1.14 away, far outside every
    // δ-window — the negated equality verifies pointwise.
    let r = run_sat(
        r#"(set-logic QF_NRT)
        (declare-const x Real)
        (assert (= (sin x) 0.0))
        (assert (>= x 3.0))
        (assert (<= x 4.0))
        (assert (distinct x 2.0))
        (check-sat)"#,
    );
    assert_eq!(r, "delta-sat", "far distinct is δ-satisfiable, got {r}");
}

#[test]
fn three_way_distinct_over_reals_decides() {
    // distinct(x, y, 0.0) under y = −x and x = sin-root-sized bounds: the
    // pairwise atoms x≠y (holds unless both 0), x≠0, y≠0.  sin(x)=0 with
    // x ∈ [3,4] pins x=π ≠ 0; y = −x ≠ 0; x ≠ y unless π = −π.  All three
    // verify — delta-sat.
    let r = run_sat(
        r#"(set-logic QF_NRT)
        (declare-const x Real)
        (declare-const y Real)
        (assert (= (sin x) 0.0))
        (assert (>= x 3.0))
        (assert (<= x 4.0))
        (assert (= y (- x)))
        (assert (distinct x y 0.0))
        (check-sat)"#,
    );
    assert_eq!(r, "delta-sat", "3-way distinct verifies, got {r}");
}

#[test]
fn distinct_of_size_two_is_negated_equality() {
    // (distinct x y) ≡ x ≠ y; with x = y asserted the negated equality's
    // box collapses onto the window and refutes.
    let r = run_sat(
        r#"(set-logic QF_NRT)
        (declare-const x Real)
        (declare-const y Real)
        (assert (= (sin x) 0.5))
        (assert (>= x 0.0))
        (assert (<= x 1.6))
        (assert (= x y))
        (assert (distinct x y))
        (check-sat)"#,
    );
    assert_eq!(r, "unsat", "distinct x y with x = y refutes, got {r}");
}

#[test]
fn nested_uninterpreted_applications_decide() {
    // f(f(x)) with x = y: the congruence chain is two implications deep
    // (x=y ⇒ f x = f y ⇒ f(f x) = f(f y)), and the inner applications
    // appear as congruence ARGUMENTS — the Ackermannization must compare
    // them through their fresh variables, not the raw `Apply` terms (the
    // raw terms declined the trans fragment and the goal floundered to
    // `unknown`).
    let r = run_sat(
        r#"(set-logic QF_NRT)
        (declare-fun f (Real) Real)
        (declare-const x Real)
        (declare-const y Real)
        (assert (= x y))
        (assert (= (exp (f (f x))) 2.0))
        (assert (= (f (f y)) 0.68))
        (check-sat)"#,
    );
    assert_eq!(r, "unsat", "nested congruence must refute, got {r}");
}
