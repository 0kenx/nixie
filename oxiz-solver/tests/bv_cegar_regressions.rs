//! CEGAR bvmul-abstraction regressions (Niemetz/Preiner/Zohar slice;
//! study `docs/studies/2026-08-bv-mul-cegar.md`).
//!
//! Every `Sat` here is only reported after the exact-product consistency
//! check AND the whole-assertion model validation, so these pin both
//! refinement tiers: the value lemma (tier 2) and the exact terminal
//! circuit (tier 3), plus the relaxation-unsat transfer (tier 1).

use oxiz_solver::Context;

fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    let out = ctx.execute_script(script).expect("script executes");
    out.iter()
        .filter(|t| !t.trim().is_empty())
        .cloned()
        .collect()
}

/// Bounded zero-divisor (both operands non-constant, so the mul is
/// abstracted, not constant-folded): `1 <= x, y < 2^32` bounds the exact
/// product below `2^64`, so `bvmul x y = 0` has no solution — but the
/// identity lemmas alone cannot see the bounds.  Refinement (value lemma
/// or terminal circuit) must transfer the refutation through the
/// relaxation.
#[test]
fn cegar_mul_bounded_zero_divisor_unsat() {
    let out = run(r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 64))
        (declare-const y (_ BitVec 64))
        (assert (bvule x (_ bv4294967295 64)))
        (assert (bvule y (_ bv4294967295 64)))
        (assert (bvule (_ bv1 64) x))
        (assert (bvule (_ bv1 64) y))
        (assert (= (bvmul x y) (_ bv0 64)))
        (check-sat)
    "#);
    assert_eq!(out, vec!["unsat"]);
}

/// `Sat` with wide muls: the reported model must satisfy the EXACT product
/// semantics — a spurious abstracted value can never pass the consistency
/// check, and the final model must evaluate every assertion true.
#[test]
fn cegar_mul_satisfiable_model_is_exact() {
    let out = run(r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 64))
        (declare-const y (_ BitVec 64))
        (declare-const z (_ BitVec 64))
        (assert (= (bvmul x y) (_ bv12 64)))
        (assert (= (bvmul y z) (_ bv20 64)))
        (assert (bvult x z))
        (check-sat)
        (get-value ((bvmul x y) (bvmul y z)))
    "#);
    assert_eq!(out[0], "sat");
    // The reported products must be the exact ones (12 = 0x0c, 20 = 0x14).
    let joined = out.join(" ");
    assert!(
        joined.contains("000000000000000c") && joined.contains("0000000000000014"),
        "got: {joined}"
    );
}

/// Low-word identity (width 32): the 32-bit product MUST equal the low
/// half of the zero-extended 64-bit product — true for every assignment,
/// so the disequality is unsat, and refuting it requires the abstraction
/// to enforce exact multiplier semantics (terminal tier or a sufficient
/// value-lemma set).  Two independent wide muls over shared operands.
#[test]
fn cegar_mul_low_word_identity_refuted() {
    let out = run(r#"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 32))
        (declare-const b (_ BitVec 32))
        (assert (not (= (bvmul a b)
                        ((_ extract 31 0)
                          (bvmul ((_ zero_extend 32) a)
                                 ((_ zero_extend 32) b))))))
        (check-sat)
    "#);
    assert_eq!(out, vec!["unsat"]);
}
