//! Z3 `bv_rewriter::mk_mul_hoist` regressions: a `bvshl` operand factors
//! out of a `bvmul` — `x · shl(z, u) → shl(x · z, u)` (multiplication is
//! associative in ℤ/2ʷ, so the shift-as-multiplication hoists outside).
//!
//! The rule closes the Noetzli rewrite-rule identities
//! (`20190311-bv-term-small-rw-Noetzli`: +52 family files decided, zero
//! regressions) whose shapes are pure mul/shl reassociations:
//!
//! * `bv-term-small-rw_1300`: `shl(s·t, s<<s) = s · shl(t, s<<s)` — both
//!   sides hoist to the same form (`bv-term-small-rw_1300_identity`).
//! * `bv-term-small-rw_1104`: `t·(s·shl(t,s)) = s·(t·shl(t,s))` — pure
//!   commutativity **after** hoisting; the hoist must flatten the
//!   shift's multiplicand into the product's factor list, or the two
//!   sides rebuild with different nesting and stop folding
//!   (`hoist_flattens_the_shift_multiplicand`).  This was a real
//!   regression during development: 1104 went 0.02 s → timeout → 0.02 s.
//! * The mirror direction (a `shl` *result* is not a mul operand) must
//!   stay untouched (`shl_result_is_not_hoisted`).

use nixie_solver::Context;

fn verdict(script: &str) -> String {
    let mut ctx = Context::new();
    let out = ctx.execute_script(script).expect("script executes");
    out.iter()
        .filter(|t| !t.trim().is_empty())
        .cloned()
        .collect::<Vec<_>>()
        .pop()
        .unwrap_or_default()
}

/// `shl(s·t, s<<s) = s · shl(t, s<<s)` over 32-bit symbolic shift
/// amounts: valid mod 2ʷ, closes through the hoist.
#[test]
fn bv_term_small_rw_1300_identity() {
    assert_eq!(
        verdict(
            r#"
            (set-logic QF_BV)
            (declare-const s (_ BitVec 32))
            (declare-const t (_ BitVec 32))
            (assert (not (= (bvshl (bvmul s t) (bvshl s s))
                            (bvmul s (bvshl t (bvshl s s))))))
            (check-sat)
        "#
        ),
        "unsat"
    );
}

/// Pure commutativity after hoisting: the hoisted shift's multiplicand is
/// itself a product (`t · shl(s·t, u)`), whose factors must join the
/// outer product's factor list — not nest.
#[test]
fn hoist_flattens_the_shift_multiplicand() {
    assert_eq!(
        verdict(
            r#"
            (set-logic QF_BV)
            (declare-const s (_ BitVec 32))
            (declare-const t (_ BitVec 32))
            (assert (not (= (bvmul t (bvmul s (bvshl t s)))
                            (bvmul s (bvmul t (bvshl t s))))))
            (check-sat)
        "#
        ),
        "unsat"
    );
}

/// Nested shifts inside the product hoist completely:
/// `s · shl(shl(t, s), s) = shl(shl(s·t, s), s)`.
#[test]
fn nested_shifts_hoist_completely() {
    assert_eq!(
        verdict(
            r#"
            (set-logic QF_BV)
            (declare-const s (_ BitVec 32))
            (declare-const t (_ BitVec 32))
            (assert (not (= (bvmul s (bvshl (bvshl t s) s))
                            (bvshl (bvshl (bvmul s t) s) s))))
            (check-sat)
        "#
        ),
        "unsat"
    );
}

/// The hoist must not apply where the shift is the *result* context, and
/// the rewrite must be a no-op for shift-free products (soundness pin on
/// the untouched path).
#[test]
fn shl_result_is_not_hoisted() {
    // (s·t) << s = s·(t << s) holds; but a NON-identity stays sat-able:
    // (s·t) << 1 ≠ s·t in general (overflow) — the hoist may not prove
    // more than associativity does.
    assert_eq!(
        verdict(
            r#"
            (set-logic QF_BV)
            (declare-const s (_ BitVec 32))
            (declare-const t (_ BitVec 32))
            (assert (= (bvshl (bvmul s t) (_ bv1 32)) (bvmul s t)))
            (check-sat)
        "#
        ),
        "sat"
    );
}

/// A hoist with a constant shift distance still composes with the
/// constant-distance shift wiring: `x · (z << 3) = (x·z) << 3`.
#[test]
fn constant_distance_hoist_composes() {
    assert_eq!(
        verdict(
            r#"
            (set-logic QF_BV)
            (declare-const x (_ BitVec 8))
            (declare-const z (_ BitVec 8))
            (assert (not (= (bvmul x (bvshl z (_ bv3 8)))
                            (bvshl (bvmul x z) (_ bv3 8)))))
            (check-sat)
        "#
        ),
        "unsat"
    );
}
