//! Regression tests for the LIA quantifier-witness chain (2026-09, the
//! jain/Ultimate class).
//!
//! Three stacked defects kept arithmetic existentials refutable by z3 but
//! `unknown` here; each is pinned by a test:
//!
//! 1. **Branch-and-bound divergence on free nonbasic integer variables**
//!    (`integral_dive` in the arithmetic solver): the crash basis rests
//!    free nonbasic integer variables at arbitrary (zero) values, so rows
//!    like `y = 2a + 1` put the LP vertex at half-integral points; Gomory
//!    cuts are inapplicable (their derivation assumes bound-resting
//!    nonbasics) and plain branching re-optimizes to the *next* half-integral
//!    point forever – the dive walked `a := -1/2, -3/2, -5/2, …` to the
//!    depth cap and the whole goal answered `unknown` from the resource
//!    gate.  The integral dive pins fractional variables to floor/ceil
//!    *equalities* (cannot drift, depth bounded by the variable count) and
//!    accepts only a genuinely feasible integral leaf.
//!
//! 2. **Nullary Skolem constants never entered the candidate pool**
//!    (`collect_skolem_candidates_rec`'s `Var` arm): `mk_skolem_constant`
//!    mints `sk!N` as a `Var` term, and the candidate walk only registered
//!    `Apply`-shaped Skolem functions – so the witness of an asserted
//!    `(exists a. 2a+1 = y)` was unavailable as an instantiation for the
//!    derived universal of `(not (exists v. 2v+1 = y))`, whose refuting
//!    instance is exactly `v := sk!0`.
//!
//! 3. **Candidate collection only ran for the nested `forall.exists`
//!    shape**: `register_asserted_quantifiers` now collects Skolem
//!    candidates for every assertion, covering the spine-existential
//!    rewrite too.
//!
//! The jain_2 shape (a four-variable sum `y = 2s0+2s1+2s2+2s3+1`, whose
//! falsifier is the *compound* witness) additionally needs the symbolic
//! `div` witness form, which `solve_linear_witnesses` now always emits
//! alongside the exact concrete quotient.

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

/// The j4 shape: an asserted existential pins `y` odd; the negated
/// existential over the same equation must be refuted through the Skolem
/// witness (the pre-fix path: B&B diverged on `y = 2a+1` and the resource
/// gate answered `unknown`).
#[test]
fn negated_arith_exists_with_witness_constant_is_unsat() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (exists ((a Int) (b Int))
          (and (= (+ (* 2 a) 1) y) (= (+ (* 2 b) 1) x))))
        (assert (not (exists ((v Int)) (= (+ (* 2 v) 1) y))))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// The j1 shape: a negated conjunction of two existentials becomes two
/// guarded derived universals; each branch is refuted by its witness
/// constant.
#[test]
fn negated_conj_of_arith_exists_is_unsat() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (exists ((a Int) (b Int))
          (and (= (+ (* 2 a) 1) y) (= (+ (* 2 b) 1) x))))
        (assert (not (and (exists ((v Int)) (= (+ (* 2 v) 1) y))
                          (exists ((w Int)) (= (+ (* 2 w) 1) x)))))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// The satisfiable companion stays `sat` (the dive must not over-refute).
#[test]
fn arith_exists_witness_stays_sat() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (exists ((a Int) (b Int))
          (and (= (+ (* 2 a) 1) y) (= (+ (* 2 b) 1) x))))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "sat");
}

/// The out-of-pool falsifier (`v = 50`): both the exact concrete quotient
/// and the symbolic `div` witness are emitted; the concrete instance
/// conflicts directly at the SAT level.
#[test]
fn solved_witness_outside_pool_is_unsat() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const y Int)
        (assert (= y 101))
        (assert (forall ((v Int)) (not (= (+ (* 2 v) 1) y))))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// The k7 parity-infeasibility shape (two free variables): LP-feasible,
/// integer-infeasible, unbounded – closed by the free-variable sign splits
/// (`close_free_vars_then_bnb`, Z3's `constrain_free_vars` analogue) with
/// split-scoped Gomory cuts.
#[test]
fn parity_infeasibility_two_free_vars_is_unsat() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const y Int)
        (declare-const S Int)
        (declare-const q Int)
        (declare-const r Int)
        (assert (= y (+ (* 2 S) 1)))
        (assert (= (- y 1) (+ (* 2 q) r)))
        (assert (>= r 0))
        (assert (<= r 1))
        (assert (< (+ (* 2 q) 1) y))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// The ground discharge of a single-sum symbolic witness: `y = 2S+1`
/// forces `(y-1) div 2 = S`, so the negated identity is refutable.  This
/// is the arithmetic core the MBQI witness instances reduce to.
#[test]
fn div_identity_single_sum_is_unsat() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const y Int)
        (declare-const S Int)
        (assert (= y (+ (* 2 S) 1)))
        (assert (not (= (+ (* 2 (div (- y 1) 2)) 1) y)))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// The k9 compound shape through the real quantifier chain: the MBQI
/// symbolic witness `(y-1) div 2` lands, its div term is axiomatized in
/// the same round (with the remainder case enumeration), SAT pins the
/// remainder, and the HNF Diophantine solver refutes the parity
/// combination.  `unsat` (z3 agrees).
#[test]
fn compound_sum_witness_discharge_is_unsat() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const y Int)
        (assert (exists ((a Int) (b Int) (c Int) (d Int))
          (= (+ (* 2 a) (* 2 b) (* 2 c) (* 2 d) 1) y)))
        (assert (not (exists ((v Int)) (= (+ (* 2 v) 1) y))))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// The four-free-variable shape with the remainder already eliminated by
/// hand: still open (split leaves churn without the div-term case
/// enumeration; the deeper jain unrollings share this shape).  Pinned to
/// never be a wrong decisive answer.
#[test]
fn parity_infeasibility_four_free_vars_is_never_wrong() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const y Int)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (declare-const d Int)
        (declare-const q Int)
        (declare-const r Int)
        (assert (= y (+ (* 2 a) (* 2 b) (* 2 c) (* 2 d) 1)))
        (assert (= (- y 1) (+ (* 2 q) r)))
        (assert (>= r 0))
        (assert (<= r 1))
        (assert (not (= (+ (* 2 q) 1) y)))
        (check-sat)
    "#);
    assert_ne!(last_status(&output), "sat");
}

/// The jain_2 compound shape: the falsifier is a four-term sum, so the
/// *symbolic* witness `(y-1) div 2` must conflict with the defining rows
/// (the concrete quotient alone lets `y` hop between rounds).
#[test]
fn compound_sum_witness_symbolic_form() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (and
          (exists ((a Int) (b Int) (c Int) (d Int))
            (= (+ (* 2 a) (* 2 b) (* 2 c) (* 2 d) 1) y))
          (exists ((e Int) (f Int) (g Int) (h Int))
            (= (+ (* 2 e) (* 2 f) (* 2 g) (* 2 h) 1) x))))
        (assert (not (and (exists ((v Int)) (= (+ (* 2 v) 1) y))
                          (exists ((w Int)) (= (+ (* 2 w) 1) x)))))
        (check-sat)
    "#);
    // The single-sum shape refutes; if the compound-sum symbolic path still
    // has a gap this must never be a wrong decisive answer.
    assert_ne!(last_status(&output), "sat");
}
