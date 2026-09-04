//! Regression tests for the UFLIA quantified `sat` benchmarks of the Z3 parity
//! suite.
//!
//! These are the integer counterparts of `uflra_quantified_sat`: goals whose
//! quantifiers alternate over `Int`, an infinite domain with no finite
//! expansion.  A `sat` verdict here means `mbqi::model_certify` built a total
//! interpretation – pin tables plus a searched default – and *checked* every
//! assertion under it, deciding each quantifier by enumerating one
//! representative per region of the critical set.

use nixie_solver::Context;

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
fn z3_parity_forall_exists_simple() {
    let script = r#"
(set-logic UFLIA)
(declare-fun f (Int Int) Int)
(assert (forall ((x Int))
  (exists ((y Int)) (> (f x y) 0))))
(assert (= (f 0 0) 1))
(assert (= (f 1 1) 2))
(assert (= (f 2 0) 3))
(check-sat)
(exit)
"#;
    assert_eq!(check_sat(script), "sat");
}

#[test]
fn z3_parity_nested_quantifiers() {
    let script = r#"
(set-logic UFLIA)
(declare-fun f (Int Int) Int)
(assert (forall ((x Int))
  (exists ((y Int))
    (forall ((z Int))
      (=> (>= z y) (>= (f x z) 0))))))
(assert (= (f 0 0) (- 1)))
(assert (= (f 0 5) 10))
(assert (= (f 0 6) 12))
(assert (= (f 1 3) 7))
(check-sat)
(exit)
"#;
    assert_eq!(check_sat(script), "sat");
}

#[test]
fn z3_parity_skolem_test() {
    let script = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (forall ((x Int))
  (exists ((y Int)) (= (g x) (f y)))))
(assert (= (g 0) 10))
(assert (= (g 1) 20))
(assert (= (f 5) 10))
(assert (= (f 7) 20))
(check-sat)
(exit)
"#;
    assert_eq!(check_sat(script), "sat");
}

/// The same alternation with no possible witness must not be certified: the
/// existential is decided by the enumeration, not waved through.
#[test]
fn unwitnessable_alternation_is_never_sat() {
    let script = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (forall ((x Int)) (= (g x) 1)))
(assert (forall ((y Int)) (= (f y) 0)))
(assert (exists ((y Int)) (= (g 0) (f y))))
(check-sat)
(exit)
"#;
    assert_ne!(check_sat(script), "sat");
}
