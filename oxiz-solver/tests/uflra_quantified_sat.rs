//! Regression tests for the UFLRA quantified `sat` benchmarks of the Z3 parity
//! suite.
//!
//! Each script here is the exact text of `bench/z3_parity/benchmarks/UFLRA/…`.
//! Every one of them is satisfiable over the reals but has no *finite* model to
//! expand: the answer comes from building a candidate interpretation (pins plus
//! an affine default, or a macro definition the goal states outright) and
//! verifying it symbolically over the whole real line.  A `sat` here therefore
//! means a model was found and checked, never that no counterexample turned up.

use oxiz_solver::Context;

/// Run `script` and return the verdict of its single `check-sat`.
fn check_sat(script: &str) -> String {
    let mut ctx = Context::new();
    let output = ctx.execute_script(script).expect("script executes");
    output
        .iter()
        .rev()
        .map(|line| line.trim().to_lowercase())
        .find(|line| line == "sat" || line == "unsat" || line == "unknown")
        .unwrap_or_else(|| format!("no verdict in {output:?}"))
}

#[test]
fn z3_parity_real_identity() {
    let script = r#"
(set-logic UFLRA)
(declare-fun f (Real) Real)
(assert (forall ((x Real)) (= (f x) x)))
(assert (= (f 3.14) 3.14))
(assert (= (f (- 2.5)) (- 2.5)))
(assert (= (f 0.0) 0.0))
(check-sat)
(exit)
"#;
    assert_eq!(check_sat(script), "sat");
}

#[test]
fn z3_parity_real_interp() {
    let script = r#"
(set-logic UFLRA)
(declare-fun f (Real) Real)
(declare-fun g (Real) Real)
(assert (forall ((x Real))
  (=> (>= x 0.0) (>= (f x) 0.0))))
(assert (forall ((x Real))
  (=> (and (>= x 0.0) (<= x 10.0))
      (<= (f x) (g x)))))
(assert (forall ((x Real))
  (=> (and (>= x 0.0) (<= x 10.0))
      (= (g x) (+ (* 2.0 x) 1.0)))))
(assert (= (f 0.0) 0.5))
(assert (= (f 5.0) 8.0))
(assert (= (g 0.0) 1.0))
(assert (= (g 5.0) 11.0))
(check-sat)
(exit)
"#;
    assert_eq!(check_sat(script), "sat");
}

#[test]
fn z3_parity_real_archimedean() {
    let script = r#"
(set-logic UFLRA)
(declare-fun ceil (Real) Real)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(declare-const n1 Real)
(declare-const n2 Real)
(declare-const n3 Real)
(assert (= x1 3.7))
(assert (= x2 (- 2.1)))
(assert (= x3 100.5))
(assert (> n1 x1))
(assert (> n2 x2))
(assert (> n3 x3))
(assert (forall ((r Real))
  (=> (and (>= r 0.0) (<= r 10.0))
      (>= (ceil r) r))))
(assert (= (ceil 3.7) 4.0))
(assert (= (ceil 0.0) 0.0))
(check-sat)
(exit)
"#;
    assert_eq!(check_sat(script), "sat");
}

#[test]
fn z3_parity_real_fixed_point() {
    let script = r#"
(set-logic UFLRA)
(declare-fun f (Real) Real)
(assert (forall ((x Real))
  (=> (and (>= x 0.0) (<= x 1.0))
      (and (>= (f x) 0.0) (<= (f x) 1.0)))))
(assert (exists ((x Real))
  (and (>= x 0.0) (<= x 1.0) (= (f x) x))))
(assert (= (f 0.5) 0.5))
(check-sat)
(exit)
"#;
    assert_eq!(check_sat(script), "sat");
}

#[test]
fn z3_parity_real_composition() {
    let script = r#"
(set-logic UFLRA)
(declare-fun f (Real) Real)
(declare-fun g (Real) Real)
(assert (forall ((x Real))
  (=> (and (>= x 0.0) (<= x 5.0))
      (= (f (g x)) (g (f x))))))
(assert (= (f 0.0) 0.0))
(assert (= (g 0.0) 0.0))
(assert (= (f 1.0) 1.0))
(assert (= (g 1.0) 1.0))
(assert (= (f 2.0) 2.0))
(assert (= (g 2.0) 2.0))
(check-sat)
(exit)
"#;
    assert_eq!(check_sat(script), "sat");
}

/// The suite's UNSAT real benchmark must stay `unsat`: a certifier that could
/// be talked into a model here would be unsound, not merely optimistic.
#[test]
fn z3_parity_real_unsat_stays_unsat() {
    let script = r#"
(set-logic UFLRA)
(declare-fun f (Real) Real)
(declare-const c Real)
(assert (forall ((x Real)) (<= (f x) 1.0)))
(assert (> (f c) 1.0))
(check-sat)
(exit)
"#;
    assert_eq!(check_sat(script), "unsat");
}

/// A pin that contradicts the quantifier is *checked*, not assumed: the
/// certifier verifies the very equation it read the pin from.
#[test]
fn pin_contradicting_its_quantifier_is_never_sat() {
    let script = r#"
(set-logic UFLRA)
(declare-fun f (Real) Real)
(assert (forall ((x Real)) (=> (> x 0.0) (> (f x) 0.0))))
(assert (= (f 1.0) 0.0))
(check-sat)
(exit)
"#;
    assert_ne!(check_sat(script), "sat");
}

/// Strict guards must be honoured exactly.  `f` is fixed to `5` on the *open*
/// interval `(0,1)` and pinned to `9` at the excluded endpoint `0`, which is
/// consistent – the certifier has to distinguish the point cell `{0}` from the
/// interval next to it rather than lumping them together.
#[test]
fn open_interval_guard_excludes_its_endpoint() {
    let script = r#"
(set-logic UFLRA)
(declare-fun f (Real) Real)
(assert (forall ((x Real))
  (=> (and (> x 0.0) (< x 1.0)) (= (f x) 5.0))))
(assert (= (f 0.0) 9.0))
(check-sat)
(exit)
"#;
    assert_eq!(check_sat(script), "sat");
}

/// The same shape with the pin *inside* the guarded interval is contradictory,
/// and must not be certified.
#[test]
fn pin_inside_open_interval_guard_is_never_sat() {
    let script = r#"
(set-logic UFLRA)
(declare-fun f (Real) Real)
(assert (forall ((x Real))
  (=> (and (> x 0.0) (< x 1.0)) (= (f x) 5.0))))
(assert (= (f 0.5) 6.0))
(check-sat)
(exit)
"#;
    assert_ne!(check_sat(script), "sat");
}

/// An existential with no witness anywhere on the line must not be certified
/// by "some cell looked true".
#[test]
fn existential_without_a_witness_is_never_sat() {
    let script = r#"
(set-logic UFLRA)
(declare-fun f (Real) Real)
(assert (forall ((x Real)) (= (f x) 1.0)))
(assert (exists ((x Real)) (= (f x) 2.0)))
(check-sat)
(exit)
"#;
    assert_ne!(check_sat(script), "sat");
}

/// Nested applications are substituted through, so a composition the goal
/// forbids cannot be certified either.
#[test]
fn contradictory_composition_is_never_sat() {
    let script = r#"
(set-logic UFLRA)
(declare-fun f (Real) Real)
(assert (forall ((x Real)) (= (f (f x)) 0.0)))
(assert (= (f 0.0) 1.0))
(assert (= (f 1.0) 1.0))
(check-sat)
(exit)
"#;
    assert_ne!(check_sat(script), "sat");
}

/// A quantified real goal with no model must not be certified into one.
#[test]
fn contradictory_bounds_are_never_certified_sat() {
    let script = r#"
(set-logic UFLRA)
(declare-fun f (Real) Real)
(assert (forall ((x Real)) (>= (f x) 1.0)))
(assert (forall ((x Real)) (<= (f x) 0.0)))
(check-sat)
(exit)
"#;
    assert_ne!(check_sat(script), "sat");
}
