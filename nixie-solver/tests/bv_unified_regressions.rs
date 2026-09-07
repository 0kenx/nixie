//! Regression tests for the BV-circuit unification campaign, Option A
//! stage 1 (`docs/handovers/2026-09-07-bv-unification.md`,
//! `nixie-solver/src/solver/bv_unified.rs`).
//!
//! The unified path is taken when a *mixed* goal (BV atoms plus something the
//! eager pure-BV dispatch refuses: an Int constraint, a Bool-result UF
//! application, ...) meets the eligibility gates.  Every test here is such a
//! mixed goal, so the default configuration exercises the unified link pass;
//! the same scripts must also hold with `NIXIE_BV_UNIFIED=0` (the lazy
//! embedded path) because the value-apart propagation fix below repairs a
//! soundness hole *both* architectures share.
//!
//! Reproductions, in the order they were found:
//!
//! * **The stale level-0 value-apart pin** (pre-existing on `main`, isolated
//!   by this campaign): a first `check-sat` whose model merges a BV variable
//!   with one ground constant propagates the *other* branch's equality atom
//!   false with an empty justification; `install_theory_units` then pins that
//!   conditional fact as a permanent level-0 unit, and a later assertion of
//!   the pinned branch is falsely refuted.  Fixed by
//!   `EufSolver::try_explain_value_apart`, which explains the apartness
//!   through the value-carrier merge proofs (empty only in the born-ground
//!   case).  The m6 shape below answered `sat, unsat` on the campaign's
//!   baseline binary and must answer `sat, sat`.
//! * **The unified two-check shape**: the same scripts through the unified
//!   generation (circuits in the main core), where the stale pins additionally
//!   froze the *bits*, made the false refutation immediate, and the mid-search
//!   `resync_theory_state` full BV reset silently ended generations.

use nixie_solver::Context;

fn verdicts(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(script)
        .expect("script should parse and run");
    out.into_iter()
        .filter(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .collect()
}

fn lines(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script)
        .expect("script should parse and run")
}

// ========  ========
// The stale level-0 value-apart pin (pre-existing soundness fix).
// ========  ========

/// The minimal reproduction on the lazy path: `or` over two BV equalities,
/// observe, then assert the branch the first model did *not* take.
///
/// Both checks are satisfiable (`v = #b0010` satisfies the second set); a
/// `unsat` second verdict means the first check's branch choice was pinned as
/// a permanent level-0 fact.  Answered `sat, unsat` on the campaign baseline
/// (30c049c lineage) through no fault of the unified path.
#[test]
fn bv_branch_pin_other_branch_stays_sat() {
    let script = r#"
        (declare-const i Int)
        (declare-const v (_ BitVec 4))
        (assert (> i 3))
        (assert (or (= v #b0010) (= v #b0111)))
        (check-sat)
        (assert (= v #b0010))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["sat", "sat"]);
}

/// Symmetric shape pinning the branch the first model *did* take (this one
/// always passed; it pins the value-apart explanation against over-reach).
#[test]
fn bv_branch_pin_same_branch_stays_sat() {
    let script = r#"
        (declare-const i Int)
        (declare-const v (_ BitVec 4))
        (assert (> i 3))
        (assert (or (= v #b0010) (= v #b0111)))
        (check-sat)
        (assert (= v #b0111))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["sat", "sat"]);
}

/// A forced first branch plus the other branch asserted later is *genuinely*
/// unsat – the fix must not lose the refutation.
#[test]
fn bv_forced_branch_then_other_is_unsat() {
    let script = r#"
        (declare-const i Int)
        (declare-const v (_ BitVec 4))
        (assert (> i 3))
        (assert (= v #b0010))
        (check-sat)
        (assert (= v #b0111))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["sat", "unsat"]);
}

/// The value-apart propagation must still *fire* (with its reason): two BV
/// ground constants under a Bool-result UF stay apart, and equating them
/// through the variable refutes.
#[test]
fn bv_value_apart_refutation_still_works() {
    let script = r#"
        (set-logic QF_UFBV)
        (declare-fun p (Bool) Bool)
        (declare-const v (_ BitVec 8))
        (assert (or (= v #x01) (= v #x02)))
        (assert (p (bvult v #x80)))
        (assert (not (= v #x01)))
        (assert (not (= v #x02)))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["unsat"]);
}

// ========  ========
// The unified path (mixed goals: general CDCL(T) + main-core circuits).
// ========  ========

/// Mixed UF(Bool)+BV chain contradiction: three comparisons in a cycle refute
/// through the linked circuits (today's lazy path refutes through the
/// embedded solver; both must agree).
#[test]
fn unified_unsigned_cycle_refutes() {
    let script = r#"
        (set-logic QF_UFBV)
        (declare-fun g ( (_ BitVec 8) ) Bool)
        (declare-const a (_ BitVec 8))
        (declare-const b (_ BitVec 8))
        (declare-const c (_ BitVec 8))
        (assert (bvult a b))
        (assert (bvult b c))
        (assert (bvult c a))
        (assert (g a))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["unsat"]);
}

/// Mixed-goal satisfiability with model readback: the unified model must
/// assign consistent bit values through the adopted main-core snapshot.
#[test]
fn unified_sat_model_readback() {
    let script = r#"
        (set-logic QF_UFBV)
        (declare-fun p (Bool) Bool)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= (bvadd x y) #x10))
        (assert (bvult x #x05))
        (assert (bvugt y #x0a))
        (assert (p (bvult x y)))
        (check-sat)
        (get-value (x y (bvadd x y)))
    "#;
    let out = lines(script);
    assert_eq!(out[0], "sat", "whole script: {out:?}");
    // The printed model must actually satisfy the constraints.
    let vals = out[1..].join(" ");
    assert!(vals.contains("#x"), "get-value returned nothing: {out:?}");
}

/// The two-check unified shape that exposed both the mid-search resync wipe
/// and the stale-pin/bits interaction: every later assertion on an already
/// linked atom must be honoured.
#[test]
fn unified_multicheck_branch_pin_stays_sat() {
    let script = r#"
        (set-logic QF_UFBV)
        (declare-fun f (Int) Int)
        (declare-const i Int)
        (declare-const v (_ BitVec 4))
        (assert (or (= i 1) (= i 5)))
        (assert (or (= v #b0010) (= v #b0111)))
        (assert (or (= (f i) 1) (= (f i) 2)))
        (check-sat)
        (assert (= i 5))
        (assert (= v #b0111))
        (assert (= (f 5) 1))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["sat", "sat"]);
}

/// `distinct` over BV in a mixed goal: the pairwise atoms are minted by the
/// `Distinct` encode arm (not sub-terms of the assertion), so they exercise
/// the constraint-sweep linking; the unsat variant needs the pair circuits.
#[test]
fn unified_distinct_mixed_sat_and_unsat() {
    let sat_script = r#"
        (set-logic QF_UFBV)
        (declare-fun w ( Bool ) Bool)
        (declare-const x0 (_ BitVec 8))
        (declare-const x1 (_ BitVec 8))
        (declare-const x2 (_ BitVec 8))
        (declare-const x3 (_ BitVec 8))
        (assert (distinct x0 x1 x2 x3))
        (assert (w true))
        (check-sat)
    "#;
    assert_eq!(verdicts(sat_script), vec!["sat"]);
    let unsat_script = r#"
        (set-logic QF_UFBV)
        (declare-fun w ( Bool ) Bool)
        (declare-const x0 (_ BitVec 8))
        (declare-const x1 (_ BitVec 8))
        (declare-const x2 (_ BitVec 8))
        (declare-const x3 (_ BitVec 8))
        (assert (distinct x0 x1 x2 x3))
        (assert (= x0 x2))
        (assert (w true))
        (check-sat)
    "#;
    assert_eq!(verdicts(unsat_script), vec!["unsat"]);
}

/// BV-result UF must fall back to the lazy path (congruence merges have no
/// clause form) and stay *correct* there.
#[test]
fn unified_falls_back_for_bv_result_uf() {
    let script = r#"
        (set-logic QF_UFBV)
        (declare-fun f (Bool) (_ BitVec 8))
        (declare-const t Bool)
        (assert (= (f t) #x01))
        (assert (= (f true) #x02))
        (assert t)
        (check-sat)
    "#;
    // f(true) cannot be both #x01 and #x02 once t is true.
    assert_eq!(verdicts(script), vec!["unsat"]);
}

/// Scoped sessions keep the lazy path from the first push (the unified gates
/// exclude scopes); both polarities must stay correct through push/pop.
#[test]
fn unified_scoped_sessions_stay_correct() {
    let script = r#"
        (set-logic QF_UFBV)
        (declare-fun p (Bool) Bool)
        (declare-const v (_ BitVec 8))
        (assert (bvult v #x10))
        (push 1)
        (assert (bvugt v #x20))
        (check-sat)
        (pop 1)
        (check-sat)
        (assert (= v #x0f))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["unsat", "sat", "sat"]);
}

/// Signed comparisons and wide constants through the unified circuits
/// (the signed-mixing and truncation land-mines from the handover).
#[test]
fn unified_signed_and_wide_constants() {
    let signed_script = r#"
        (set-logic QF_UFBV)
        (declare-fun p (Bool) Bool)
        (declare-const x (_ BitVec 8))
        (assert (bvslt x #x7f))
        (assert (bvsgt x #x00))
        (assert (p true))
        (check-sat)
        (assert (bvsge x #x7f))
        (check-sat)
    "#;
    // x in (0, 127) signed, then x >= 127 signed: contradiction.
    assert_eq!(verdicts(signed_script), vec!["sat", "unsat"]);

    let wide_script = r#"
        (set-logic QF_UFBV)
        (declare-fun p (Bool) Bool)
        (declare-const x (_ BitVec 128))
        (assert (= x #xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF))
        (assert (bvult x #x00000000000000000000000000000001))
        (assert (p true))
        (check-sat)
    "#;
    assert_eq!(verdicts(wide_script), vec!["unsat"]);
}

/// The `bvsmod`/ite desugaring battery through the unified path: the BV
/// operators lower to BV-sorted `ite`s inside the term builder, and hoisting
/// them once produced a false `sat` (see `needs_ite_elimination`'s comment).
#[test]
fn unified_smod_roundtrip() {
    let script = r#"
        (set-logic QF_UFBV)
        (declare-fun q (Bool) Bool)
        (declare-const x (_ BitVec 8))
        (declare-const s (_ BitVec 8))
        (assert (= s (bvsmod x #x03)))
        (assert (= x #x07))
        (assert (= s #x02))
        (assert (q true))
        (check-sat)
    "#;
    // 7 smod 3 = 1, so s = 2 is unsat.
    assert_eq!(verdicts(script), vec!["unsat"]);
    let sat_script = r#"
        (set-logic QF_UFBV)
        (declare-fun q (Bool) Bool)
        (declare-const x (_ BitVec 8))
        (declare-const s (_ BitVec 8))
        (assert (= s (bvsmod x #x03)))
        (assert (= x #x07))
        (assert (= s #x01))
        (assert (q true))
        (check-sat)
    "#;
    assert_eq!(verdicts(sat_script), vec!["sat"]);
}
