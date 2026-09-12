//! Gate structural hash-consing (`NIXIE_BV_GATE_SH=1`) regressions.
//!
//! The gate constructors memoize on canonical input-var pairs, so identical
//! gates share one output variable and one clause set — z3's expression-level
//! sharing at the gate layer.  It closes the "same product, two encodings"
//! class (`2017-BuchwaldFried/Mul32·Mulh_u32`: high-half of a 96-bit mul of
//! zero-extended operands vs a 64-bit mul — both cascade residues close in
//! ~0.1 s under the flag, timeout without) and cracks two multiplier cells
//! outright (`smulov2bw064` 1.5 s, `umulov1bw064`).
//!
//! Soundness posture (why this is safe): entries are inserted **only at the
//! base scope** (`BvSolver::at_base_scope` — the same invariant that keeps
//! `term_to_bv` truthful), so a memo var's defining clauses are permanent;
//! unified-era entries are wiped on `enter_unified`/`exit_unified`/`reset`
//! alongside the other var-space-carrying tables.  Scoped (mid-search)
//! builds never insert, so a popped clause can never leave a stale entry.
//!
//! These tests pin: the sharing identities, pop/re-push correctness around
//! gate-reused circuits, and that the flag's shared vars survive a
//! check/pop/check sequence with correct verdicts.

use nixie_solver::Context;

fn gate_sh_on() {
    #[cfg(feature = "std")]
    // SAFETY: this test binary owns its process (per-test processes under
    // `cargo nextest`; every test here sets the same value first).
    unsafe { std::env::set_var("NIXIE_BV_GATE_SH", "1") };
}

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

/// The BuchwaldFried shape: the high half of a 96-bit product of
/// zero-extended operands equals the high half of the 64-bit product —
/// both multipliers share every partial product and adder, and the
/// equality folds.
#[test]
fn shared_gates_close_reencoded_product_identity() {
    gate_sh_on();
    assert_eq!(
        verdict(r#"
            (set-logic QF_BV)
            (declare-const x (_ BitVec 32))
            (declare-const y (_ BitVec 32))
            (assert (not (= ((_ extract 63 32) (bvmul (concat #x00000000 x) (concat #x00000000 y)))
                            ((_ extract 63 32) (bvmul (concat #x0000000000000000 x)
                                                      (concat #x0000000000000000 y))))))
            (check-sat)
        "#),
        "unsat"
    );
}

/// A second, differently-spelled sharing shape (bit-gathered operand).
#[test]
fn shared_gates_close_bitgathered_product() {
    gate_sh_on();
    assert_eq!(
        verdict(r#"
            (set-logic QF_BV)
            (declare-const w (_ BitVec 36))
            (declare-const x (_ BitVec 32))
            (assert (not (= ((_ extract 63 32)
                              (bvmul (concat #x00000000 x)
                                     (concat #x00000000 (concat (concat (concat ((_ extract 34 27) w)
                                                                          ((_ extract 25 18) w))
                                                                     ((_ extract 16 9) w))
                                                            ((_ extract 7 0) w)))))
                            ((_ extract 63 32)
                              (bvmul (concat #x0000000000000000 x)
                                     (concat #x0000000000000000 (concat (concat (concat ((_ extract 34 27) w)
                                                                                      ((_ extract 25 18) w))
                                                                             ((_ extract 16 9) w))
                                                                    ((_ extract 7 0) w))))))))
            (check-sat)
        "#),
        "unsat"
    );
}

/// Scoped correctness: gate-reused circuits built at one scope must not
/// leak wrong definitions across a pop.  A definition-heavy goal is
/// checked, popped, and re-checked with a contradictory second conjunct —
/// the popped scope's facts must not survive into the re-check.
#[test]
fn shared_gates_respect_pop_scopes() {
    gate_sh_on();
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            r#"
            (set-logic QF_BV)
            (declare-const a (_ BitVec 16))
            (declare-const b (_ BitVec 16))
            (push 1)
            (assert (= (bvmul a b) (_ bv6 16)))
            (assert (= a (_ bv2 16)))
            (check-sat)
            (pop 1)
            ;; Without the popped facts, a·b = 6 alone is satisfiable …
            (assert (= (bvmul a b) (_ bv6 16)))
            (check-sat)
            ;; … and contradicting the popped scope's a = 2 must be fine.
            (assert (= a (_ bv3 16)))
            (check-sat)
        "#,
        )
        .expect("script executes");
    let v: Vec<&str> = out.iter().map(String::as_str).collect();
    assert_eq!(v, vec!["sat", "sat", "sat"], "verdicts: {out:?}");
}

/// The smulov2bw064 shape: sign-extended products whose overflow detector
/// shares the multiplier across the two encodings.  Pinned at a small
/// width with concrete operands so the verdict is exact.
#[test]
fn shared_gates_sign_extended_product_grid() {
    gate_sh_on();
    for (x, y, p) in [(2u32, 3u32, 6u32), (7u32, 9u32, 63u32), (1u32, 12u32, 12u32)] {
        let script = format!(
            "(set-logic QF_BV)\n\
             (declare-const x (_ BitVec 12))\n\
             (declare-const y (_ BitVec 12))\n\
             (assert (= x (_ bv{x} 12)))\n\
             (assert (= y (_ bv{y} 12)))\n\
             (assert (= (bvmul (concat (_ bv0 12) x) (concat (_ bv0 12) y)) (_ bv{p} 24)))\n\
             (check-sat)"
        );
        assert_eq!(verdict(&script), "sat", "{x}·{y} = {p}");
        let wrong = p ^ 2;
        let script = format!(
            "(set-logic QF_BV)\n\
             (declare-const x (_ BitVec 12))\n\
             (declare-const y (_ BitVec 12))\n\
             (assert (= x (_ bv{x} 12)))\n\
             (assert (= y (_ bv{y} 12)))\n\
             (assert (= (bvmul (concat (_ bv0 12) x) (concat (_ bv0 12) y)) (_ bv{wrong} 24)))\n\
             (check-sat)"
        );
        assert_eq!(verdict(&script), "unsat", "{x}·{y} != {wrong}");
    }
}
