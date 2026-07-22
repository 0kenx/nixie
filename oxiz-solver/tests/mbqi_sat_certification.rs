//! End-to-end regression tests for MBQI SAT certification over the
//! (almost-)uninterpreted / bounded fragment that UFLIA / UFLRA / AUFLIA target.
//!
//! These pin the behaviour implemented in `oxiz-solver/src/mbqi/sat_certify.rs`
//! plus its wiring in `mbqi/integration.rs`: for a satisfiable quantified goal
//! whose universal quantifiers fall in the complete-instantiation fragment, the
//! solver must saturate the relevant/bounded instantiation set and answer `sat`
//! rather than `unknown`.  The `*_unsat` tests are the soundness half — the same
//! machinery must never turn a genuinely unsatisfiable quantified goal into a
//! spurious `sat` (a universal instance is only ever a sound consequence).
//!
//! Each script mirrors the shape of a `bench/z3_parity` benchmark family so a
//! regression here corresponds directly to a parity loss.

use oxiz_solver::Context;

/// Run a full SMT-LIB script and return the first `sat` / `unsat` / `unknown`
/// line it prints.
fn check(script: &str) -> String {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(script)
        .expect("script should parse and run");
    out.into_iter()
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| "<no check-sat output>".to_string())
}

// ---------------------------------------------------------------------------
// SAT certification: satisfiable quantified goals must return `sat`.
// ---------------------------------------------------------------------------

/// Bounded-box fragment: an injectivity axiom over a finite integer window,
/// consistent with the ground function values.  This is the regression guard
/// for the spurious-`unsat` bug where the raw (unsimplified) guarded box
/// instances fed the downstream pigeonhole / integer-domain heuristics a bogus
/// "bounded variable" shape.
#[test]
fn uflia_injective_bounded_box_sat() {
    let r = check(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int) (y Int))
          (=> (and (>= x 0) (<= x 10) (>= y 0) (<= y 10) (= (f x) (f y)))
              (= x y))))
        (assert (= (f 1) 10))
        (assert (= (f 2) 20))
        (assert (= (f 3) 30))
        (check-sat)
    "#,
    );
    assert_eq!(r, "sat", "bounded-box injectivity should certify sat");
}

/// Essentially-uninterpreted fragment with a monotonicity axiom whose bound
/// variables appear only under the uninterpreted `f`; certified by instantiating
/// over the ground argument terms `{0, 5, 10}`.
#[test]
fn uflia_monotone_relevant_terms_sat() {
    let r = check(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int) (y Int)) (=> (<= x y) (<= (f x) (f y)))))
        (assert (= (f 0) 0))
        (assert (= (f 10) 100))
        (assert (>= (f 5) 30))
        (assert (<= (f 5) 70))
        (check-sat)
    "#,
    );
    assert_eq!(r, "sat", "monotone UF axiom should certify sat");
}

/// Two bounded-box quantifiers sharing an integer window `[0, n)` with `n = 3`,
/// with a sum constraint over the enumerated elements.
#[test]
fn uflia_sum_bounds_int_box_sat() {
    let r = check(
        r#"
        (set-logic UFLIA)
        (declare-fun a (Int) Int)
        (declare-const n Int)
        (assert (forall ((i Int)) (=> (and (>= i 0) (< i n)) (>= (a i) 0))))
        (assert (= n 3))
        (assert (= (+ (a 0) (+ (a 1) (a 2))) 10))
        (assert (forall ((i Int)) (=> (and (>= i 0) (< i n)) (<= (a i) 5))))
        (check-sat)
    "#,
    );
    assert_eq!(r, "sat", "bounded sum axiom should certify sat");
}

/// Real essentially-uninterpreted fragment: `f` is range-bounded for every real,
/// with each bound variable appearing only as an argument of `f`.
#[test]
fn uflra_bounds_essentially_uninterpreted_sat() {
    let r = check(
        r#"
        (set-logic UFLRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real)) (and (>= (f x) 0.0) (<= (f x) 1.0))))
        (assert (= (f 0.0) 0.5))
        (assert (= (f 1.0) 0.75))
        (assert (= (f (- 1.0)) 0.25))
        (check-sat)
    "#,
    );
    assert_eq!(r, "sat", "real range-bound axiom should certify sat");
}

/// Real monotone axiom with a variable-vs-variable `<=` guard (the
/// monotone-preserving almost-uninterpreted case).
#[test]
fn uflra_monotone_var_var_guard_sat() {
    let r = check(
        r#"
        (set-logic UFLRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real) (y Real)) (=> (<= x y) (<= (f x) (f y)))))
        (assert (= (f 0.0) 0.0))
        (assert (= (f 1.0) 2.5))
        (assert (= (f 3.0) 7.0))
        (check-sat)
    "#,
    );
    assert_eq!(r, "sat", "real monotone axiom should certify sat");
}

/// Almost-uninterpreted fragment: real Lipschitz bound with variable-vs-ground
/// interval guards `0 <= x <= 5`, consequent reads the variables only through
/// `f`.  The guard constants `{0, 5}` are folded into the relevant set.
#[test]
fn uflra_lipschitz_almost_uninterpreted_sat() {
    let r = check(
        r#"
        (set-logic UFLRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real) (y Real))
          (=> (and (>= x 0.0) (<= x 5.0) (>= y 0.0) (<= y 5.0))
              (and (<= (- (f x) (f y)) 10.0)
                   (<= (- (f y) (f x)) 10.0)))))
        (assert (= (f 0.0) 0.0))
        (assert (= (f 1.0) 1.5))
        (assert (= (f 3.0) 4.0))
        (check-sat)
    "#,
    );
    assert_eq!(r, "sat", "real Lipschitz axiom should certify sat");
}

/// Array bounded-box: every index in `[0, n)` initialised to 0, `n = 5`.
#[test]
fn auflia_forall_init_bounded_box_sat() {
    let r = check(
        r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const n Int)
        (assert (= n 5))
        (assert (forall ((i Int)) (=> (and (>= i 0) (< i n)) (= (select a i) 0))))
        (assert (= (select a 0) 0))
        (assert (= (select a 4) 0))
        (check-sat)
    "#,
    );
    assert_eq!(r, "sat", "bounded array-init axiom should certify sat");
}

/// Array sortedness with a mixed guard: a variable-vs-variable `i <= j` bound
/// together with variable-vs-ground `0 <= i` and `j < n`.  Consequent compares
/// only `select` values.
#[test]
fn auflia_sorted_mixed_guard_sat() {
    let r = check(
        r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const n Int)
        (assert (= n 4))
        (assert (forall ((i Int) (j Int))
          (=> (and (>= i 0) (<= i j) (< j n))
              (<= (select a i) (select a j)))))
        (assert (= (select a 0) 1))
        (assert (= (select a 1) 3))
        (assert (= (select a 2) 5))
        (assert (= (select a 3) 7))
        (check-sat)
    "#,
    );
    assert_eq!(r, "sat", "sorted-array axiom should certify sat");
}

/// Array update via a disequality guard `i != k`: everything but the updated
/// index is preserved.  Exercises the disequality-vs-ground guard path.
#[test]
fn auflia_update_disequality_guard_sat() {
    let r = check(
        r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const k Int)
        (declare-const v Int)
        (assert (= b (store a k v)))
        (assert (= k 3))
        (assert (= v 99))
        (assert (forall ((i Int)) (=> (not (= i k)) (= (select b i) (select a i)))))
        (assert (= (select a 0) 10))
        (assert (= (select a 1) 20))
        (assert (= (select b 3) 99))
        (check-sat)
    "#,
    );
    assert_eq!(r, "sat", "array-update axiom should certify sat");
}

// ---------------------------------------------------------------------------
// Soundness: unsatisfiable quantified goals must never be certified `sat`.
// ---------------------------------------------------------------------------

/// A point the guard admits (`x = 7`) that is *not* a function-argument term,
/// whose consequent forces `f(7)` to be simultaneously `>= 5` and `<= 2`.  This
/// is the case that the guard-constant augmentation of the relevant set exists
/// to catch: without adding `7` the instance would be missed and the goal
/// wrongly certified `sat`.
#[test]
fn uflia_guard_constant_trap_unsat() {
    let r = check(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (=> (= x 7) (and (>= (f x) (f 3)) (<= (f x) (f 1))))))
        (assert (= (f 3) 5))
        (assert (= (f 1) 2))
        (check-sat)
    "#,
    );
    assert_ne!(r, "sat", "guard-constant trap must not be certified sat");
}

/// Bounded-box axiom with an in-range violation: `f(2) = -1` contradicts
/// `forall x in [0,3]. f(x) >= 0`.
#[test]
fn uflia_bounded_box_violation_unsat() {
    let r = check(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (=> (and (>= x 0) (<= x 3)) (>= (f x) 0))))
        (assert (= (f 2) (- 1)))
        (check-sat)
    "#,
    );
    assert_eq!(r, "unsat", "in-range bounded violation must be unsat");
}

/// Real bounded-region violation: `f(3) = 20` contradicts
/// `forall x in [0,5]. f(x) <= 10`.
#[test]
fn uflra_bounded_region_violation_unsat() {
    let r = check(
        r#"
        (set-logic UFLRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real)) (=> (and (>= x 0.0) (<= x 5.0)) (<= (f x) 10.0))))
        (assert (= (f 3.0) 20.0))
        (check-sat)
    "#,
    );
    assert_ne!(r, "sat", "in-region real violation must not be sat");
    assert_eq!(r, "unsat");
}

/// The mirror of the previous test: the violating fact `f(7) = 20` lies
/// *outside* the guard region `[0,5]`, so the goal is genuinely satisfiable and
/// must stay `sat` (the certifier must not over-approximate the guard).
#[test]
fn uflra_out_of_region_fact_sat() {
    let r = check(
        r#"
        (set-logic UFLRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real)) (=> (and (>= x 0.0) (<= x 5.0)) (<= (f x) 10.0))))
        (assert (= (f 7.0) 20.0))
        (check-sat)
    "#,
    );
    assert_eq!(r, "sat", "out-of-region fact should remain sat");
}

/// Array bounded-box with an in-range violation: `a[2] = -5` contradicts
/// `forall i in [0,4). a[i] >= 0`.
#[test]
fn auflia_bounded_array_violation_unsat() {
    let r = check(
        r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))
        (assert (forall ((i Int)) (=> (and (>= i 0) (< i 4)) (>= (select a i) 0))))
        (assert (= (select a 2) (- 5)))
        (check-sat)
    "#,
    );
    assert_eq!(r, "unsat", "in-range array violation must be unsat");
}

/// Monotone axiom violated by a mid-range inversion (`f(0) = 5 > 3 = f(1)`),
/// which the essentially-uninterpreted relevant-term instantiation refutes.
#[test]
fn uflia_monotone_violation_unsat() {
    let r = check(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int) (y Int)) (=> (<= x y) (<= (f x) (f y)))))
        (assert (= (f 0) 5))
        (assert (= (f 1) 3))
        (check-sat)
    "#,
    );
    assert_eq!(r, "unsat", "monotone inversion must be unsat");
}

/// The classic MBQI refutation: `forall x. f(x) >= 0` together with a ground
/// `f(a) < 0` must be `unsat` via instantiation at `x = a`.  Guards that the SAT
/// certification path did not disturb refutational completeness.
#[test]
fn uflia_forall_ground_conflict_unsat() {
    let r = check(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (assert (forall ((x Int)) (>= (f x) 0)))
        (assert (< (f a) 0))
        (check-sat)
    "#,
    );
    assert_eq!(r, "unsat", "forall/ground conflict must be unsat");
}
