//! Certified-mode SAT over uninterpreted functions and sorts.
//!
//! Before the 2026-09 UF-model-certificate extension, every `Sat` verdict on
//! a formula mentioning uninterpreted functions failed closed to `unknown`:
//! the certificate model carried no values for uninterpreted-sort terms, so
//! `CachedEvaluator` could not evaluate an assertion containing `(f x)`.
//! The certificate now completes uninterpreted-sort constants and
//! applications with EUF-class witnesses (`@uc_S_n`, exactly the
//! `get-model` synthesis) and — before accepting — independently verifies
//! the resulting function table is well-defined (congruent arguments map to
//! equal results). See `nixie-solver/src/solver/certification.rs`.
//!
//! The `_unsat` half pins the fail-closed direction: a contradiction that
//! needs congruence semantics still returns `unknown` from certified mode
//! (the Boolean skeleton alone is satisfiable).

use nixie_solver::Context;

fn check_certified(script: &str) -> String {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(script)
        .expect("script should parse and run");
    out.into_iter()
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| "<no check-sat output>".to_string())
}

/// Pure QF_UF with applications under equalities over an uninterpreted
/// sort: satisfiable, and the certificate must evaluate `(op a b)`-style
/// applications plus `distinct` and accept `sat`.
#[test]
fn certified_qfuf_sat_with_applications() {
    let r = check_certified(
        "(set-logic QF_UF)
         (set-option :certified-mode true)
         (declare-sort S 0)
         (declare-fun f (S) S)
         (declare-fun a () S)
         (declare-fun b () S)
         (declare-fun c () S)
         (assert (distinct a b c))
         (assert (= (f a) c))
         (assert (= (f b) (f a)))
         (assert (not (= (f c) b)))
         (check-sat)",
    );
    assert_eq!(r, "sat");
}

/// `distinct` alone over an uninterpreted sort (the QG/iso benchmark shape):
/// the evaluator's `Distinct` arm over `Uninterpreted` witnesses must fire.
#[test]
fn certified_qfuf_distinct_only_sat() {
    let r = check_certified(
        "(set-logic QF_UF)
         (set-option :certified-mode true)
         (declare-sort S 0)
         (declare-const e0 S)
         (declare-const e1 S)
         (declare-const e2 S)
         (declare-const e3 S)
         (assert (distinct e0 e1 e2 e3))
         (check-sat)",
    );
    assert_eq!(r, "sat");
}

/// Binary function applications nested under a chain of equalities: the
/// congruence-well-definedness check must accept a consistent table.
#[test]
fn certified_qfuf_binary_ops_sat() {
    let r = check_certified(
        "(set-logic QF_UF)
         (set-option :certified-mode true)
         (declare-sort I 0)
         (declare-fun op (I I) I)
         (declare-const e0 I)
         (declare-const e1 I)
         (declare-const e2 I)
         (assert (distinct e0 e1 e2))
         (assert (= (op e0 e1) e2))
         (assert (= (op e1 e0) e2))
         (assert (= (op e2 e2) e0))
         (assert (not (= (op e0 e0) (op e1 e1))))
         (check-sat)",
    );
    assert_eq!(r, "sat");
}

/// Congruence-dependent contradiction: `a = b` forces `(f a) = (f b)`, so
/// the formula is UNSAT through congruence semantics. Since the EUF
/// theory-lemma certificates landed (2026-09), certified mode ACCEPTS this:
/// the search's congruence lemma `¬(a=b) ∨ f(a)=f(b)` is recorded, verified
/// by the gate's independent congruence closure, and the skeleton+lemma
/// set is refuted by LRAT. (Before: failed closed to `unknown`.)
#[test]
fn certified_qfuf_congruence_unsat_certifies() {
    let r = check_certified(
        "(set-logic QF_UF)
         (set-option :certified-mode true)
         (declare-sort S 0)
         (declare-fun f (S) S)
         (declare-const a S)
         (declare-const b S)
         (assert (= a b))
         (assert (not (= (f a) (f b))))
         (check-sat)",
    );
    assert_eq!(r, "unsat");
}

/// A congruence contradiction that runs through `distinct` and a
/// transitivity chain: the gate's structural `distinct ⇒ pairwise ¬Eq`
/// encoding must link the disequality facts to the lemma literals.
#[test]
fn certified_qfuf_distinct_transitivity_unsat_certifies() {
    let r = check_certified(
        "(set-logic QF_UF)
         (set-option :certified-mode true)
         (declare-sort S 0)
         (declare-fun f (S) S)
         (declare-const a S)
         (declare-const b S)
         (declare-const c S)
         (assert (distinct a b c))
         (assert (= a b))
         (assert (not (= (f c) (f a))))
         (check-sat)",
    );
    assert_eq!(r, "unsat");
}

/// Arithmetic equalities certify since the LP verifier landed
/// (`verify_lia_lemma`): `(= x 1) ∧ (= x 2)` is LP-infeasible by exact
/// substitution, so the recorded lemma verifies and the gate refutes
/// skeleton + lemma. (Before the LIA slice this failed closed to
/// `unknown` — congruence closure cannot verify arithmetic.)
#[test]
fn certified_qflia_eq_unsat_certifies() {
    let r = check_certified(
        "(set-logic QF_LIA)
         (set-option :certified-mode true)
         (declare-const x Int)
         (assert (= x 1))
         (assert (= x 2))
         (check-sat)",
    );
    assert_eq!(r, "unsat");
}

/// A bound collision through linear arithmetic: `y ≥ x+2 ∧ x ≥ 5 ∧ y ≤ 6`
/// is LP-infeasible (substitution + Fourier–Motzkin), so the recorded
/// lemmas verify and certified mode accepts `unsat`.
#[test]
fn certified_qflia_bound_conflict_certifies() {
    let r = check_certified(
        "(set-logic QF_LIA)
         (set-option :certified-mode true)
         (declare-const x Int)
         (declare-const y Int)
         (assert (>= y (+ x 2)))
         (assert (>= x 5))
         (assert (<= y 6))
         (check-sat)",
    );
    assert_eq!(r, "unsat");
}

/// The LP verifier's documented completeness boundary: parity-only
/// infeasibility (`x = 2y+1 ∧ x = 2z`) is rational-feasible, so the
/// lemmas cannot verify and certified mode fails closed to `unknown` —
/// never a wrong verdict.
#[test]
fn certified_qflia_parity_boundary_stays_unknown() {
    let r = check_certified(
        "(set-logic QF_LIA)
         (set-option :certified-mode true)
         (declare-const x Int)
         (declare-const y Int)
         (declare-const z Int)
         (assert (= x (+ (* 2 y) 1)))
         (assert (= x (* 2 z)))
         (check-sat)",
    );
    assert_eq!(r, "unknown");
}

/// A satisfiable formula whose witnesses sit inside `ite` branches of an
/// uninterpreted sort: the certificate evaluates `ite` structurally, so the
/// branch constants must carry the synthesized witnesses.
#[test]
fn certified_qfuf_ite_over_uninterpreted_sat() {
    let r = check_certified(
        "(set-logic QF_UF)
         (set-option :certified-mode true)
         (declare-sort S 0)
         (declare-fun f (S) S)
         (declare-const a S)
         (declare-const b S)
         (declare-const p Bool)
         (assert (distinct a b))
         (assert (= (ite p a b) a))
         (assert (= (f (ite p a b)) b))
         (check-sat)",
    );
    assert_eq!(r, "sat");
}

/// Regressions for the pre-existing coverage: integer `sat` models and
/// Boolean-skeleton `unsat` refutations keep certifying after the UF
/// extension (the new arms must not perturb them).
#[test]
fn certified_qflia_sat_and_boolean_unsat_unchanged() {
    let sat = check_certified(
        "(set-logic QF_LIA)
         (set-option :certified-mode true)
         (declare-const x Int)
         (assert (> x 3))
         (assert (< x 10))
         (check-sat)",
    );
    assert_eq!(sat, "sat");

    let unsat = check_certified(
        "(set-logic QF_UF)
         (set-option :certified-mode true)
         (declare-const p Bool)
         (assert p)
         (assert (not p))
         (check-sat)",
    );
    assert_eq!(unsat, "unsat");
}

/// A Bool-returning function's congruence contradiction (the eq_diamond /
/// NEQ family shape): `a = b` forces `p(a) = p(b)` as Booleans, so
/// `p(a) ∧ ¬p(b) ∧ a=b` is unsat. The lemma atoms are Bool-sorted
/// applications — recordable since the 2026-09 extension that treats them
/// as equalities against the Boolean constants.
#[test]
fn certified_qfuf_bool_function_congruence_unsat_certifies() {
    let r = check_certified(
        "(set-logic QF_UF)
         (set-option :certified-mode true)
         (declare-sort S 0)
         (declare-fun p (S) Bool)
         (declare-const a S)
         (declare-const b S)
         (assert (= a b))
         (assert (p a))
         (assert (not (p b)))
         (check-sat)",
    );
    assert_eq!(r, "unsat");
}

/// A refutation that needs a disequality fact (`distinct x 5` splits the
/// integers): the LP verifier branches over the disequality — both sides
/// infeasible — and certified mode accepts `unsat`.
#[test]
fn certified_qflia_disequality_refutation_certifies() {
    let r = check_certified(
        "(set-logic QF_LIA)
         (set-option :certified-mode true)
         (declare-const x Int)
         (assert (distinct x 5))
         (assert (<= x 4))
         (assert (>= x 6))
         (check-sat)",
    );
    assert_eq!(r, "unsat");
}
