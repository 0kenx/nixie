//! End-to-end regression tests for finite-range quantifier expansion.
//!
//! A quantifier whose own guard pins every bound Int variable to a concrete
//! finite interval is rewritten at assert time into the *logically equivalent*
//! finite conjunction (`forall`) / disjunction (`exists`) over that interval –
//! see `oxiz-solver/src/solver/encode/finite_expand.rs`.  The quantifier then
//! disappears entirely and the ordinary ground solver decides the problem, so
//! `sat` here is a genuine ground model, not an MBQI guess.
//!
//! Two halves are pinned:
//!
//! * `*_sat` – the satisfiable goals the expansion makes decidable, including
//!   the three `bench/z3_parity/benchmarks/AUFLIA` scripts the capability was
//!   built for (`z3_parity_*`);
//! * `*_unsat` / soundness – the same machinery must never turn a satisfiable
//!   goal into a spurious `unsat` (the rewrite is an equivalence, so *both*
//!   directions are pinned), and must decline every shape whose bounds are not
//!   provably concrete.

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

// ========  ========
// The z3_parity AUFLIA benchmarks this capability targets.
// ========  ========

/// `bench/z3_parity/benchmarks/AUFLIA/array_search.smt2`.
///
/// `∃i ∈ [0, 9]. a[i] = v` with `v = 42` and `a[5] = 42` pinned: the expansion
/// turns the existential into a ten-way disjunction whose fifth disjunct the
/// ground array solver satisfies outright.
#[test]
fn z3_parity_array_search() {
    let r = check(
        r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const v Int)
        (assert (= v 42))
        (assert (exists ((i Int))
          (and (>= i 0) (<= i 9) (= (select a i) v))))
        (assert (= (select a 0) 10))
        (assert (= (select a 1) 20))
        (assert (= (select a 5) 42))
        (assert (= (select a 9) 90))
        (check-sat)
    "#,
    );
    assert_eq!(r, "sat", "the witness i = 5 is pinned by the assertions");
}

/// `bench/z3_parity/benchmarks/AUFLIA/array_permutation.smt2`.
///
/// Three existentials over `[0, 2]`, each expanded into a three-way
/// disjunction; together with the range and distinctness constraints the ground
/// solver must find the permutation.
#[test]
fn z3_parity_array_permutation() {
    let r = check(
        r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))
        (assert (and (>= (select a 0) 1) (<= (select a 0) 3)))
        (assert (and (>= (select a 1) 1) (<= (select a 1) 3)))
        (assert (and (>= (select a 2) 1) (<= (select a 2) 3)))
        (assert (not (= (select a 0) (select a 1))))
        (assert (not (= (select a 1) (select a 2))))
        (assert (not (= (select a 0) (select a 2))))
        (assert (exists ((i Int)) (and (>= i 0) (<= i 2) (= (select a i) 1))))
        (assert (exists ((i Int)) (and (>= i 0) (<= i 2) (= (select a i) 2))))
        (assert (exists ((i Int)) (and (>= i 0) (<= i 2) (= (select a i) 3))))
        (check-sat)
    "#,
    );
    assert_eq!(r, "sat", "a permutation of 1, 2, 3 exists");
}

/// `bench/z3_parity/benchmarks/AUFLIA/array_max.smt2`.
///
/// Mixes both directions and a *symbolic* bound: the guard is `i < n` with
/// `(assert (= n 5))`, so the interval is only concrete because the entailed
/// constant `n = 5` is folded in.
#[test]
fn z3_parity_array_max() {
    let r = check(
        r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const n Int)
        (declare-const m Int)
        (assert (= n 5))
        (assert (forall ((i Int))
          (=> (and (>= i 0) (< i n))
              (<= (select a i) m))))
        (assert (exists ((j Int))
          (and (>= j 0) (< j n) (= (select a j) m))))
        (assert (= (select a 0) 3))
        (assert (= (select a 1) 7))
        (assert (= (select a 2) 1))
        (assert (= (select a 3) 9))
        (assert (= (select a 4) 5))
        (assert (= m 9))
        (check-sat)
    "#,
    );
    assert_eq!(r, "sat", "m = 9 is the maximum, achieved at j = 3");
}

// ========  ========
// Soundness: the expansion is an equivalence, so `unsat` must survive it.
// ========  ========

/// The same existential shape as `array_search`, but with every index in range
/// pinned to a different value: no witness exists and the expanded disjunction
/// must be refuted.
#[test]
fn bounded_exists_without_witness_unsat() {
    let r = check(
        r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))
        (assert (exists ((i Int)) (and (>= i 0) (<= i 2) (= (select a i) 42))))
        (assert (= (select a 0) 1))
        (assert (= (select a 1) 2))
        (assert (= (select a 2) 3))
        (check-sat)
    "#,
    );
    assert_eq!(r, "unsat", "no index in [0,2] holds 42");
}

/// A universal over a concrete box whose instance at `i = 3` contradicts a
/// ground fact.  The expansion must expose that conflict.
#[test]
fn bounded_forall_violated_instance_unsat() {
    let r = check(
        r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))
        (assert (forall ((i Int)) (=> (and (< 0 i) (> 5 i)) (<= (select a i) 100))))
        (assert (= (select a 3) 700))
        (check-sat)
    "#,
    );
    assert_eq!(r, "unsat", "a[3] = 700 violates the bounded upper bound");
}

/// The *satisfiable* companion of the previous test, with the same reversed and
/// strict comparison forms (`(< 0 i)`, `(> 5 i)`), pinning that the interval is
/// read as `[1, 4]` rather than being mis-oriented.
#[test]
fn bounded_forall_strict_reversed_bounds_sat() {
    let r = check(
        r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))
        (assert (forall ((i Int)) (=> (and (< 0 i) (> 5 i)) (<= (select a i) 100))))
        (assert (= (select a 1) 7))
        (assert (= (select a 4) 3))
        (assert (= (select a 5) 900))
        (check-sat)
    "#,
    );
    assert_eq!(
        r, "sat",
        "index 5 is outside [1,4], so a[5] = 900 is unconstrained"
    );
}

/// A multi-variable box (3 × 3 = 9 instances) in both directions.
#[test]
fn multi_variable_box_sat_and_unsat() {
    let script = |fact: &str| {
        format!(
            r#"
            (set-logic UFLIA)
            (declare-fun f (Int Int) Int)
            (assert (forall ((i Int) (j Int))
              (=> (and (>= i 0) (<= i 2) (>= j 0) (<= j 2)) (<= (f i j) 9))))
            {fact}
            (check-sat)
        "#
        )
    };
    assert_eq!(check(&script("(assert (= (f 1 1) 4))")), "sat");
    assert_eq!(check(&script("(assert (= (f 1 2) 40))")), "unsat");
}

// ========  ========
// Polarity: the rewrite is an equivalence, so it is legal under a negation too.
// ========  ========

/// `¬∃x ∈ [0, 2]. f(x) = 7` together with `f(1) = 7` is unsatisfiable.  A
/// rewrite that merely *strengthened* or *weakened* the existential instead of
/// preserving it would lose this.
#[test]
fn negated_bounded_exists_unsat() {
    let r = check(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (not (exists ((x Int)) (and (>= x 0) (<= x 2) (= (f x) 7)))))
        (assert (= (f 1) 7))
        (check-sat)
    "#,
    );
    assert_eq!(r, "unsat");
}

/// The same negated existential stays satisfiable when the witness sits outside
/// the interval.
#[test]
fn negated_bounded_exists_outside_range_sat() {
    let r = check(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (not (exists ((x Int)) (and (>= x 0) (<= x 2) (= (f x) 7)))))
        (assert (= (f 3) 7))
        (check-sat)
    "#,
    );
    assert_eq!(r, "sat");
}

// ========  ========
// Nesting: an inner quantifier that reads the outer bound variable.
// ========  ========

/// `∀i ∈ [0,1]. ∃j ∈ [0,1]. a[j] = i` with `a = [0, 1]` – satisfiable.
#[test]
fn nested_bounded_quantifiers_sat() {
    let r = check(
        r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))
        (assert (forall ((i Int)) (=> (and (>= i 0) (<= i 1))
          (exists ((j Int)) (and (>= j 0) (<= j 1) (= (select a j) i))))))
        (assert (= (select a 0) 0))
        (assert (= (select a 1) 1))
        (check-sat)
    "#,
    );
    assert_eq!(r, "sat");
}

/// The unsatisfiable companion – and the direct regression guard for the
/// capture hazard: splicing the inner existential's expansion in place while it
/// still mentions the outer `i` makes the capture-avoiding substituter
/// alpha-rename the `∀`, which turned `i` into a free constant and answered
/// `sat` for this very script.
#[test]
fn nested_bounded_quantifiers_unsat() {
    let r = check(
        r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))
        (assert (forall ((i Int)) (=> (and (>= i 0) (<= i 1))
          (exists ((j Int)) (and (>= j 0) (<= j 1) (= (select a j) i))))))
        (assert (= (select a 0) 5))
        (assert (= (select a 1) 6))
        (check-sat)
    "#,
    );
    assert_eq!(r, "unsat", "neither a[0] nor a[1] can equal 0");
}

// ========  ========
// Empty ranges.
// ========  ========

/// `∀x ∈ ∅` constrains nothing: the goal stays satisfiable even though the
/// consequent is contradicted at a point outside the (empty) range.
#[test]
fn empty_range_forall_is_vacuous_sat() {
    let r = check(
        r#"
        (set-logic UFLIA)
        (declare-fun p (Int) Bool)
        (assert (forall ((x Int)) (=> (and (>= x 5) (<= x 2)) (p x))))
        (assert (not (p 5)))
        (check-sat)
    "#,
    );
    assert_eq!(r, "sat", "an empty universal range imposes nothing");
}

/// `∃x ∈ ∅` has no witness, so asserting it is outright unsatisfiable.
#[test]
fn empty_range_exists_is_unsat() {
    let r = check(
        r#"
        (set-logic UFLIA)
        (declare-fun p (Int) Bool)
        (assert (exists ((x Int)) (and (>= x 5) (<= x 2) (p x))))
        (check-sat)
    "#,
    );
    assert_eq!(r, "unsat", "an empty existential range has no witness");
}

// ========  ========
// Fall-through: shapes the expansion must decline.
// ========  ========

/// A 201-point interval exceeds the default budget of 64, so the quantifier
/// keeps its ordinary MBQI path.  Whatever that path concludes, it must never
/// be `unsat`: the goal is satisfiable (`a[5] = 42` witnesses it).
#[test]
fn over_budget_range_falls_through_without_unsoundness() {
    let r = check(
        r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))
        (assert (exists ((i Int)) (and (>= i 0) (<= i 200) (= (select a i) 42))))
        (assert (= (select a 5) 42))
        (check-sat)
    "#,
    );
    assert_ne!(
        r, "unsat",
        "a satisfiable goal must not be refuted on the fall-through path"
    );
}

/// An unconstrained symbolic bound is not a concrete interval, so nothing is
/// expanded – `n` could be arbitrarily large and the witness arbitrarily far
/// out.  Refuting this would be unsound.
#[test]
fn unpinned_symbolic_bound_falls_through_without_unsoundness() {
    let r = check(
        r#"
        (set-logic UFLIA)
        (declare-fun p (Int) Bool)
        (declare-const n Int)
        (assert (exists ((i Int)) (and (>= i 0) (< i n) (p i))))
        (assert (not (p 0)))
        (assert (not (p 1)))
        (assert (not (p 2)))
        (check-sat)
    "#,
    );
    assert_ne!(r, "unsat", "the witness may lie at any index below n");
}

/// The entailed-constant map must not outlive the scope that justified it: a
/// popped `(assert (= n 3))` may not turn a later `(< i n)` into the interval
/// `[0, 2]`, which would refute this satisfiable goal.
#[test]
fn popped_entailed_constant_is_not_reused() {
    let r = check(
        r#"
        (set-logic UFLIA)
        (declare-fun p (Int) Bool)
        (declare-const n Int)
        (push 1)
        (assert (= n 3))
        (pop 1)
        (assert (exists ((i Int)) (and (>= i 0) (< i n) (p i))))
        (assert (not (p 0)))
        (assert (not (p 1)))
        (assert (not (p 2)))
        (check-sat)
    "#,
    );
    assert_ne!(
        r, "unsat",
        "n is unconstrained after the pop, so the witness may be any index"
    );
}

/// A live entailed constant *is* used, in both directions: with `n = 3` the
/// interval is `[0, 2]` and the pinned array refutes the existential.
#[test]
fn entailed_constant_bound_is_used() {
    let sat = check(
        r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const n Int)
        (assert (= n 3))
        (assert (exists ((i Int)) (and (>= i 0) (< i n) (= (select a i) 9))))
        (assert (= (select a 0) 1))
        (assert (= (select a 1) 9))
        (assert (= (select a 2) 3))
        (check-sat)
    "#,
    );
    assert_eq!(sat, "sat", "a[1] = 9 witnesses the existential");

    let unsat = check(
        r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const n Int)
        (assert (= n 3))
        (assert (exists ((i Int)) (and (>= i 0) (< i n) (= (select a i) 9))))
        (assert (= (select a 0) 1))
        (assert (= (select a 1) 2))
        (assert (= (select a 2) 3))
        (check-sat)
    "#,
    );
    assert_eq!(unsat, "unsat", "no index below n = 3 holds 9");
}

/// A guard that only *partially* bounds the variable (upper bound but no lower
/// bound) is not a finite interval and must be declined.
#[test]
fn half_bounded_guard_falls_through_without_unsoundness() {
    let r = check(
        r#"
        (set-logic UFLIA)
        (declare-fun p (Int) Bool)
        (assert (exists ((i Int)) (and (<= i 2) (p i))))
        (assert (not (p 0)))
        (assert (not (p 1)))
        (assert (not (p 2)))
        (check-sat)
    "#,
    );
    assert_ne!(
        r, "unsat",
        "negative indices are still in range, so the goal is satisfiable"
    );
}
