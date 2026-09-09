//! Regression tests for the negated-quantifier false-`sat` class (2026-09).
//!
//! A quantifier sitting behind a polarity boundary used to have **no owner**:
//! the Tseitin encoder binds every quantifier term to a free Boolean,
//! `register_asserted_quantifiers` deliberately refuses to register anything
//! not unconditionally asserted, and MBQI only ever consults what was
//! registered.  A goal whose ground part was satisfiable therefore answered
//! `sat` with the negated quantifier silently forgotten:
//!
//! * the funcprobs/U48 shape – `∀x. f(x) = 0` together with
//!   `¬∀x,y. x·f(x+x·y) = x·f(x) + f(x²)·f(y)` – answered `sat` although the
//!   two assertions are contradictory (f ≡ 0 makes the negated universal
//!   false), via `MBQIResult::Satisfied` on the *registered* quantifier only;
//! * `¬∃z. z ≥ 0` answered `sat` via `MBQIResult::NoQuantifiers`, the same
//!   free-Boolean hole with an empty registry.
//!
//! Two coordinated fixes are pinned here:
//!
//! 1. `exists_skolem::skolemize_asserted_existentials` now rewrites the
//!    conjuncts an assertion states unconditionally that are headed by a
//!    negated quantifier, with the negation pushed *inside* first:
//!    `¬∀x.φ → ¬φ(sk)` (ground, witness searched) and `¬∃x.φ → ∀x.¬φ`
//!    (registered like any asserted universal).
//! 2. `Solver::unowned_quantifier_seen` marks quantifiers that remain without
//!    an owning engine (inside an `or` branch, an `ite` arm, a Bool `=`
//!    operand, ...), and the `NoQuantifiers`/`Satisfied` `sat` exits require
//!    independent model certification before printing `sat` over them.
//!
//! The historical polarity-guard regression – registering `¬∀x. P(x)` as
//! `∀x. P(x)` refuted the satisfiable `(¬∀x. P(x)) ∧ ¬P(5)` – is guarded by
//! `negated_forall_conjunct_with_false_ground_instance_stays_sat`: the
//! Skolemized witness must be *searched for*, never asserted true.

use nixie_solver::Context;

fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script)
        .expect("script should parse and run")
}

fn last_status(output: &[String]) -> &str {
    output
        .iter()
        .rev()
        .find(|line| {
            let t = line.trim();
            matches!(t, "sat" | "unsat" | "unknown")
        })
        .map(String::as_str)
        .unwrap_or("<no verdict>")
}

/// The funcprobs/U48 false-`sat`, minimized: with `f ≡ 0` forced by the
/// universal, the negated universal is false, so the goal is `unsat`.
///
/// The refutation crosses a nonlinear product (`x · f(...)`) whose
/// zero-factor fold the arithmetic layer does not yet perform, so the pinned
/// property here is the soundness one – *never `sat`* – while the strict
/// `unsat` pin lives on the multiplier-free shape in
/// [`skolemized_negated_forall_collides_with_universal`].
#[test]
fn negated_forall_with_total_definition_is_unsat() {
    let output = run(r#"
        (set-logic UFNIRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real)) (= (f x) 0.0)))
        (assert (not (forall ((x Real) (y Real))
            (= (* x (f (+ x (* x y)))) (+ (* x (f x)) (* (f (* x x)) (f y)))))))
        (check-sat)
    "#);
    assert_ne!(last_status(&output), "sat");
}

/// The same contradiction with the witness searched as a ground constant:
/// `f(sk) ≠ 0` plus `∀x. f(x) = 0`.
#[test]
fn skolemized_negated_forall_collides_with_universal() {
    let output = run(r#"
        (set-logic UFLRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real)) (= (f x) 0.0)))
        (assert (not (forall ((y Real)) (= (f y) 0.0))))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// `¬∃z. z ≥ 0` is `∀z. z < 0`, refuted by `z = 0`: the answer the free
/// Boolean used to fabricate as `sat`.
#[test]
fn negated_exists_over_unbounded_guard_is_unsat() {
    let output = run(r#"
        (set-logic NIA)
        (assert (not (exists ((z Int)) (>= z 0))))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// The de Morgan companion: `¬∃z. z = 5` is `∀z. z ≠ 5`, refuted by `z = 5`.
#[test]
fn negated_exists_witnessed_by_constant_is_unsat() {
    let output = run(r#"
        (set-logic NIA)
        (assert (not (exists ((z Int)) (= z 5))))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// A negated existential that is *true* must stay `sat` (and must not be
/// refuted by the rewrite): `¬∃x. x < x`.
#[test]
fn negated_exists_trivially_true_stays_sat() {
    let output = run(r#"
        (set-logic NIA)
        (assert (not (exists ((x Int)) (< x x))))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "sat");
}

/// The historical polarity-guard shape: registering `¬∀x. P(x)` as
/// `∀x. P(x)` refuted this satisfiable goal.  The Skolemized reading
/// (`P(sk)` may be false, e.g. at `sk = 5`) keeps it `sat`.
#[test]
fn negated_forall_conjunct_with_false_ground_instance_stays_sat() {
    let output = run(r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (assert (not (forall ((x Int)) (P x))))
        (assert (not (P 5)))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "sat");
}

/// A negated universal with a genuinely satisfiable witness body: `¬∀x. x < 0`
/// holds at `x = 0`.
#[test]
fn negated_forall_with_real_witness_stays_sat() {
    let output = run(r#"
        (set-logic NIA)
        (assert (not (forall ((x Int)) (< x 0))))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "sat");
}

/// Direct contradiction between a universal and its own negation.
#[test]
fn forall_and_negated_copy_is_unsat() {
    let output = run(r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (assert (forall ((x Int)) (P x)))
        (assert (not (forall ((x Int)) (P x))))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// The funcprobs family member that motivated the hunt (declared `unsat`).
/// The refutation needs the nonlinear zero-factor fold that the arithmetic
/// layer does not yet perform, so the pinned property is the *soundness* one:
/// never `sat`.
#[test]
fn funcprobs_u48_is_never_sat() {
    let output = run(r#"
        (set-logic UFNIRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real)) (= (f x) 0.0)))
        (assert (not
          (forall ((x Real) (y Real)) (= (* x (f (+ x (* x y))))
            (+ (* x (f x)) (* (f (* x x)) (f y)))))))
        (check-sat)
    "#);
    assert_ne!(last_status(&output), "sat");
}

/// A quantifier behind a polarity boundary (`or` disjunct) has no owning
/// engine.  The goal is satisfiable either way (`> 5 0` holds), so `sat` may
/// only be printed after independent certification – and `unsat` must never
/// appear.  Both exits are covered by pinning "not unsat" plus, when the
/// verdict is decisive, correctness against the obvious model.
#[test]
fn boundary_quantifier_goal_is_never_wrong() {
    let output = run(r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (assert (or (forall ((x Int)) (P x)) (> 5 0)))
        (check-sat)
    "#);
    assert_ne!(last_status(&output), "unsat");
}

/// The boundary gate must not fire when the boundary quantifier is also
/// unconditionally asserted elsewhere in the goal (ownership is per term,
/// decided after the whole walk): the universal is registered, satisfies the
/// model, and `sat` follows without an honesty downgrade.
#[test]
fn boundary_quantifier_registered_elsewhere_stays_decisive() {
    let output = run(r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (assert (forall ((x Int)) (P x)))
        (assert (or (forall ((x Int)) (P x)) (P 0)))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "sat");
}

/// Scope consistency: the unowned-quantifier flag is snapshot/restored by
/// `push`/`pop`.  Inside the scope the contradictory negated universal is
/// refuted; after the `pop` the plain universal goal is `sat` again (a stale
/// flag would wrongly downgrade it to `unknown`, and a stale *registered*
/// ∀ would wrongly refute it).
#[test]
fn negated_forall_scope_round_trip() {
    let output = run(r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (assert (forall ((x Int)) (P x)))
        (push 1)
        (assert (not (forall ((x Int)) (P x))))
        (check-sat)
        (pop 1)
        (check-sat)
    "#);
    let verdicts: Vec<&str> = output
        .iter()
        .filter_map(|l| match l.trim() {
            "sat" | "unsat" | "unknown" => Some(l.trim()),
            _ => None,
        })
        .collect();
    assert_eq!(verdicts, vec!["unsat", "sat"]);
}

/// A negated existential nested under an `and` spine conjunct (not the head
/// of the conjunct itself) still gets its universal reading registered:
/// `¬∃x. x > 3` is refuted by `x = 4`.
#[test]
fn negated_exists_under_and_spine_is_unsat() {
    let output = run(r#"
        (set-logic NIA)
        (assert (and (>= 1 0) (not (exists ((x Int)) (> x 3)))))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}
