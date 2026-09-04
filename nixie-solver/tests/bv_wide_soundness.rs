//! Regression tests for bit-vectors wider than 64 bits.
//!
//! Everything here failed before the wide-BV fixes, and every failure had the
//! same root cause: a 64-bit window onto an arbitrary-width value.
//!
//! | Script                                                   | Was      | Must be |
//! |----------------------------------------------------------|----------|---------|
//! | `x = 2^64` ∧ `x <u 1` at width 128                        | `sat`    | `unsat` |
//! | `a = 0`, `b = 2^64`, `(distinct (g a) (g b))` at 128      | `unsat`  | `sat`   |
//! | `(get-value (x))` for a 96-bit `x` pinned to all-ones     | `#x00…0` | exact   |
//!
//! 1. The bit-blaster pinned a `BitVecConst` from `iter_u64_digits().next()`,
//!    so a 128-bit constant became its low limb: `2^64` was asserted as `0`,
//!    which really is `<u 1` – a false `sat` in release builds, and a shift
//!    overflow abort in debug ones.
//! 2. The EUF canonicalisation of BV constants keyed on `(low_64_bits, width)`,
//!    so `0` and `2^64` shared a key at width 128 and were *merged* – with the
//!    merge recorded as tautological.  Congruence then made `(g a)` and `(g b)`
//!    the same node and the disequality became a conflict: a false `unsat`.
//! 3. The model builder read `BvSolver::get_value`, which is `None` above 64
//!    bits, so every wide bit-vector fell through to a default of `0`.
//!
//! The equal-value direction of (2) is pinned as well: two *distinct* term ids
//! holding the same wide constant must still be merged, or the fix would have
//! traded a false `unsat` for a lost congruence.

use nixie_solver::{Context, SolverResult};

/// Run a single SMT-LIB2 script and return the solver result.
///
/// The verdict is the last `sat` / `unsat` / `unknown` token in the output.
fn run_script(script: &str) -> SolverResult {
    let mut ctx = Context::new();
    let outputs = ctx.execute_script(script).unwrap_or_default();
    for tok in outputs.iter().rev() {
        match tok.trim() {
            "sat" => return SolverResult::Sat,
            "unsat" => return SolverResult::Unsat,
            "unknown" => return SolverResult::Unknown,
            _ => {}
        }
    }
    SolverResult::Unknown
}

/// Every output line of a script, so `(get-value ...)` can be inspected.
fn run_script_output(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script).unwrap_or_default()
}

// ========  ========
// 1. Wide constants must be pinned at their full width
// ========  ========

/// `x = 2^64 ∧ x <u 1` at width 128.  Truncating the constant to its low limb
/// pinned `x = 0`, which satisfies `x <u 1`: a false `sat`.
#[test]
fn wide_const_high_limb_is_pinned_128bit() {
    let script = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 128))
(assert (= x (_ bv18446744073709551616 128)))
(assert (bvult x (_ bv1 128)))
(check-sat)
";
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// The satisfiable twin: nothing about the fix may turn a real `sat` into
/// `unsat`.  `2^64 <u 2^64 + 1` holds at width 128.
#[test]
fn wide_const_high_limb_stays_sat_when_satisfiable_128bit() {
    let script = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 128))
(assert (= x (_ bv18446744073709551616 128)))
(assert (bvult x (_ bv18446744073709551617 128)))
(check-sat)
";
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Two wide constants that differ *only* above bit 64 must be unequal.
#[test]
fn wide_consts_differing_above_bit_64_are_unequal() {
    let script = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 128))
(assert (= x (_ bv0 128)))
(assert (= x (_ bv18446744073709551616 128)))
(check-sat)
";
    assert_eq!(run_script(script), SolverResult::Unsat);
}

// ========  ========
// 2. EUF canonicalisation of wide BV constants
// ========  ========

/// Distinct wide constants sharing their low 64 bits must stay in distinct EUF
/// classes, so `(distinct (g a) (g b))` is satisfiable.
#[test]
fn distinct_wide_consts_are_not_merged_in_euf() {
    let script = "\
(set-logic QF_UFBV)
(declare-fun g ((_ BitVec 128)) (_ BitVec 8))
(declare-const a (_ BitVec 128))
(declare-const b (_ BitVec 128))
(assert (= a (_ bv0 128)))
(assert (= b (_ bv18446744073709551616 128)))
(assert (distinct (g a) (g b)))
(check-sat)
";
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// The other direction: *equal* wide constants must still be merged, so
/// congruence closure still derives `(g a) = (g b)` and the disequality is a
/// conflict.  Without this the full-value key would have cost a real `unsat`.
#[test]
fn equal_wide_consts_still_merge_in_euf() {
    let script = "\
(set-logic QF_UFBV)
(declare-fun g ((_ BitVec 128)) (_ BitVec 8))
(declare-const a (_ BitVec 128))
(declare-const b (_ BitVec 128))
(assert (= a (_ bv18446744073709551616 128)))
(assert (= b (_ bv18446744073709551616 128)))
(assert (distinct (g a) (g b)))
(check-sat)
";
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// The same congruence conflict one limb up, so the discriminating bits sit
/// above 64 on *both* sides of the key.
#[test]
fn wide_const_congruence_conflict_above_bit_64() {
    let script = "\
(set-logic QF_UFBV)
(declare-fun g ((_ BitVec 128)) (_ BitVec 8))
(declare-const a (_ BitVec 128))
(declare-const b (_ BitVec 128))
(assert (= a (_ bv36893488147419103232 128)))
(assert (= b (_ bv36893488147419103232 128)))
(assert (distinct (g a) (g b)))
(check-sat)
";
    assert_eq!(run_script(script), SolverResult::Unsat);
}

// ========  ========
// 3. Wide model values
// ========  ========

/// A 96-bit variable pinned to all-ones must be *reported* as all-ones; the
/// model used to read `0` because `get_value` gives up above 64 bits.
#[test]
fn wide_bv_model_value_round_trips_96bit() {
    let script = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 96))
(assert (= x (_ bv79228162514264337593543950335 96)))
(check-sat)
(get-value (x))
";
    let outputs = run_script_output(script);
    let printed = outputs.join("\n");
    assert!(
        printed.contains("#xffffffffffffffffffffffff"),
        "96-bit model value must be the pinned constant, got: {printed}"
    );
}

/// A value whose *only* set bit lives above 64: the low limb is zero, so a
/// 64-bit read cannot tell it apart from `0`.
#[test]
fn wide_bv_model_value_high_limb_only_128bit() {
    let script = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 128))
(assert (= x (_ bv18446744073709551616 128)))
(check-sat)
(get-value (x))
";
    let outputs = run_script_output(script);
    let printed = outputs.join("\n");
    assert!(
        printed.contains("#x00000000000000010000000000000000"),
        "128-bit model value must carry the high limb, got: {printed}"
    );
}

// ========  ========
// 4. Wide BV structure must not abort or answer falsely
// ========  ========

/// `2^64 + 2^64 = 2^65` at width 128 – a carry that crosses the limb boundary.
#[test]
fn wide_bv_add_crosses_limb_boundary_128bit() {
    let script = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 128))
(assert (= x (_ bv18446744073709551616 128)))
(assert (not (= (bvadd x x) (_ bv36893488147419103232 128))))
(check-sat)
";
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// A mixed-width application is malformed, but it must never abort the process
/// and must never be answered `unsat` on the strength of a bogus circuit.
#[test]
fn mixed_width_bv_op_does_not_abort() {
    let script = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 16))
(assert (= (bvadd x y) y))
(check-sat)
";
    assert_ne!(run_script(script), SolverResult::Unsat);
}
