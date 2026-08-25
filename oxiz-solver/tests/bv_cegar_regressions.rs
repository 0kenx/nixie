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

/// `run` with division abstraction enabled (`OXIZ_BV_CEGAR_DIV=64`): the
/// div tests below must exercise the *abstraction*, not silently fall back
/// to the exact circuits (division CEGAR is sound but ships default-off —
/// a measured negative on the available corpus).  `set_var` is process-
/// global but safe here: nextest runs each test in its own process, and
/// even under a threaded runner the only tests in this binary are the six
/// CEGAR ones, for which this variable only *widens* abstraction (never
/// changes a verdict — the relaxation argument).
fn run_div(script: &str) -> Vec<String> {
    // SAFETY: see doc comment.
    unsafe { std::env::set_var("OXIZ_BV_CEGAR_DIV", "64") };
    let out = run(script);
    // SAFETY: see doc comment.
    unsafe { std::env::remove_var("OXIZ_BV_CEGAR_DIV") };
    out
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

/// Division abstraction — SMT-LIB zero-divisor semantics are wired as EXACT
/// tier-1 lemmas: `bvudiv a 0 = 1…1` and `bvurem a 0 = a`.  Denying either
/// under a provably-zero divisor is unsat with no refinement at all.
#[test]
fn cegar_div_zero_divisor_semantics_exact() {
    let out = run_div(
        r#"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 64))
        (declare-const b (_ BitVec 64))
        (assert (= b (_ bv0 64)))
        (assert (not (= (bvudiv a b) (_ bv18446744073709551615 64))))
        (assert (not (= (bvurem a b) a)))
        (check-sat)
    "#,
    );
    assert_eq!(out, vec!["unsat"]);
}

/// Division abstraction — satisfiable model must carry the EXACT quotient
/// and remainder (the tier-2 consistency check enforces `7·5 + 3 = 38`).
#[test]
fn cegar_div_satisfiable_model_is_exact() {
    let out = run_div(
        r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 64))
        (assert (= (bvurem x (_ bv7 64)) (_ bv3 64)))
        (assert (= (bvudiv x (_ bv7 64)) (_ bv5 64)))
        (check-sat)
        (get-value ((bvurem x (_ bv7 64)) (bvudiv x (_ bv7 64))))
    "#,
    );
    assert_eq!(out[0], "sat");
    let joined = out.join(" ");
    assert!(
        joined.contains("0000000000000003") && joined.contains("0000000000000005"),
        "got: {joined}"
    );
}

/// Division identity equation (unsat through refinement): with every
/// operand bounded below 16, `q·b + r = a ∧ r < b` cannot wrap, so the
/// Euclidean uniqueness theorem pins `q = a bvudiv b` and `r = a bvurem b`;
/// denying either requires the exact division semantics (refinement tiers).
/// (The bounds on `q` are load-bearing: without them `q·b + r` can wrap
/// mod 2^64 and the identity has spurious solutions — verified against z3.)
#[test]
fn cegar_div_identity_equation_unsat() {
    let out = run_div(
        r#"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 64))
        (declare-const b (_ BitVec 64))
        (declare-const q (_ BitVec 64))
        (declare-const r (_ BitVec 64))
        (assert (= (bvadd (bvmul q b) r) a))
        (assert (bvult r b))
        (assert (bvuge a (_ bv1 64)))
        (assert (bvuge b (_ bv1 64)))
        (assert (bvule a (_ bv15 64)))
        (assert (bvule b (_ bv15 64)))
        (assert (bvule q (_ bv15 64)))
        (assert (not (= q (bvudiv a b))))
        (assert (not (= r (bvurem a b))))
        (check-sat)
    "#,
    );
    assert_eq!(out, vec!["unsat"]);
}
