//! Audit regression tests for the BV theory bit-blaster.
//!
//! Covers two confirmed soundness defects:
//!
//! 1. Barrel shifters (`bvshl`/`bvlshr`/`bvashr`) ignored the high bits of the
//!    shift amount, so a shift amount whose only set bits were above
//!    `ilog2(width)` was treated as a shift by 0 (identity) instead of the
//!    SMT-LIB result (0 for shl/lshr, sign-fill for ashr).
//!
//! 2. Division/remainder (`bvudiv`/`bvurem`/`bvsdiv`/`bvsrem`) admitted spurious
//!    quotients because the equation `a = q*b + r` was only enforced modulo
//!    `2^w` (the final adder carry-out was dropped), letting `q*b + r` wrap.

use nixie_core::ast::TermId;
use nixie_theories::bv::BvSolver;
use nixie_theories::{Theory, TheoryCheckResult};

fn is_sat(r: &TheoryCheckResult) -> bool {
    matches!(r, TheoryCheckResult::Sat)
}

fn is_unsat(r: &TheoryCheckResult) -> bool {
    matches!(r, TheoryCheckResult::Unsat(_))
}

// ======== Barrel-shifter over-shift ========

/// `bvshl 0xFF #x10` on width 8: shift amount 16 (bit 4 set) is >= width, so
/// the result must be 0, not the identity `0xFF` the buggy encoder produced.
#[test]
fn shl_overshift_yields_zero() {
    let mut solver = BvSolver::new();
    let (x, s, res) = (TermId::new(1), TermId::new(2), TermId::new(3));
    solver.new_bv(x, 8);
    solver.new_bv(s, 8);
    solver.assert_const(x, 0xFF, 8);
    solver.assert_const(s, 16, 8);
    solver.bv_shl(res, x, s);
    solver.assert_const(res, 0, 8);
    assert!(
        is_sat(&solver.check().expect("check")),
        "shl by 16 must be 0"
    );
}

/// The identity result must now be rejected for the same over-shift.
#[test]
fn shl_overshift_is_not_identity() {
    let mut solver = BvSolver::new();
    let (x, s, res) = (TermId::new(1), TermId::new(2), TermId::new(3));
    solver.new_bv(x, 8);
    solver.new_bv(s, 8);
    solver.assert_const(x, 0xFF, 8);
    solver.assert_const(s, 16, 8);
    solver.bv_shl(res, x, s);
    solver.assert_const(res, 0xFF, 8);
    assert!(
        is_unsat(&solver.check().expect("check")),
        "shl by 16 must not equal the input"
    );
}

/// `bvlshr 0xFF #x10` on width 8 must be 0.
#[test]
fn lshr_overshift_yields_zero() {
    let mut solver = BvSolver::new();
    let (x, s, res) = (TermId::new(1), TermId::new(2), TermId::new(3));
    solver.new_bv(x, 8);
    solver.new_bv(s, 8);
    solver.assert_const(x, 0xFF, 8);
    solver.assert_const(s, 16, 8);
    solver.bv_lshr(res, x, s);
    solver.assert_const(res, 0, 8);
    assert!(
        is_sat(&solver.check().expect("check")),
        "lshr by 16 must be 0"
    );
}

/// `bvashr 0x80 #x10` on width 8: `0x80` is negative, so the over-shift result
/// must be sign-fill = `0xFF`, not the identity `0x80`.
#[test]
fn ashr_overshift_yields_sign_fill() {
    let mut solver = BvSolver::new();
    let (x, s, res) = (TermId::new(1), TermId::new(2), TermId::new(3));
    solver.new_bv(x, 8);
    solver.new_bv(s, 8);
    solver.assert_const(x, 0x80, 8);
    solver.assert_const(s, 16, 8);
    solver.bv_ashr(res, x, s);
    solver.assert_const(res, 0xFF, 8);
    assert!(
        is_sat(&solver.check().expect("check")),
        "ashr of a negative value by 16 must be all-ones"
    );
}

/// Over-shift of a non-negative value under `bvashr` yields 0.
#[test]
fn ashr_overshift_nonneg_yields_zero() {
    let mut solver = BvSolver::new();
    let (x, s, res) = (TermId::new(1), TermId::new(2), TermId::new(3));
    solver.new_bv(x, 8);
    solver.new_bv(s, 8);
    solver.assert_const(x, 0x7F, 8);
    solver.assert_const(s, 16, 8);
    solver.bv_ashr(res, x, s);
    solver.assert_const(res, 0, 8);
    assert!(is_sat(&solver.check().expect("check")));
}

/// Sanity: an in-range shift still works (`1 << 3 == 8`), so the over-shift
/// wiring did not regress the normal path.
#[test]
fn shl_in_range_still_correct() {
    let mut solver = BvSolver::new();
    let (x, s, res) = (TermId::new(1), TermId::new(2), TermId::new(3));
    solver.new_bv(x, 8);
    solver.new_bv(s, 8);
    solver.assert_const(x, 1, 8);
    solver.assert_const(s, 3, 8);
    solver.bv_shl(res, x, s);
    solver.assert_const(res, 8, 8);
    assert!(is_sat(&solver.check().expect("check")));
}

// ======== Division/remainder no-wrap ========

/// The headline finding: width 4, `bvudiv #b0001 #b0011` (1 / 3) has quotient 0.
/// The spurious quotient 5 (which only satisfied the equation via the wrap
/// `5*3 + 2 = 17 ≡ 1 mod 16`) must now be rejected.
#[test]
fn udiv_rejects_wrapping_quotient() {
    let mut solver = BvSolver::new();
    let (x, y, q) = (TermId::new(1), TermId::new(2), TermId::new(3));
    solver.new_bv(x, 4);
    solver.new_bv(y, 4);
    solver.assert_const(x, 1, 4);
    solver.assert_const(y, 3, 4);
    solver.bv_udiv(q, x, y);
    solver.assert_const(q, 5, 4);
    assert!(
        is_unsat(&solver.check().expect("check")),
        "q=5 only works via a mod-16 wrap and must be rejected"
    );
}

/// The correct quotient 0 for 1 / 3 (width 4) remains satisfiable.
#[test]
fn udiv_accepts_correct_quotient() {
    let mut solver = BvSolver::new();
    let (x, y, q) = (TermId::new(1), TermId::new(2), TermId::new(3));
    solver.new_bv(x, 4);
    solver.new_bv(y, 4);
    solver.assert_const(x, 1, 4);
    solver.assert_const(y, 3, 4);
    solver.bv_udiv(q, x, y);
    solver.assert_const(q, 0, 4);
    assert!(is_sat(&solver.check().expect("check")));
}

/// `bvurem #b0001 #b0011` (1 % 3, width 4) is 1. The wrapping witness that
/// yielded remainder 2 must now be rejected.
#[test]
fn urem_rejects_wrapping_remainder() {
    let mut solver = BvSolver::new();
    let (x, y, rem) = (TermId::new(1), TermId::new(2), TermId::new(3));
    solver.new_bv(x, 4);
    solver.new_bv(y, 4);
    solver.assert_const(x, 1, 4);
    solver.assert_const(y, 3, 4);
    solver.bv_urem(rem, x, y);
    solver.assert_const(rem, 2, 4);
    assert!(
        is_unsat(&solver.check().expect("check")),
        "remainder 2 for 1%3 is only reachable via wrap"
    );
}

/// The correct remainder 1 for 1 % 3 (width 4) remains satisfiable.
#[test]
fn urem_accepts_correct_remainder() {
    let mut solver = BvSolver::new();
    let (x, y, rem) = (TermId::new(1), TermId::new(2), TermId::new(3));
    solver.new_bv(x, 4);
    solver.new_bv(y, 4);
    solver.assert_const(x, 1, 4);
    solver.assert_const(y, 3, 4);
    solver.bv_urem(rem, x, y);
    solver.assert_const(rem, 1, 4);
    assert!(is_sat(&solver.check().expect("check")));
}

/// Divide-by-zero conventions still hold: `bvudiv x 0 = all-ones`.
#[test]
fn udiv_by_zero_is_all_ones() {
    let mut solver = BvSolver::new();
    let (x, y, q) = (TermId::new(1), TermId::new(2), TermId::new(3));
    solver.new_bv(x, 4);
    solver.new_bv(y, 4);
    solver.assert_const(x, 5, 4);
    solver.assert_const(y, 0, 4);
    solver.bv_udiv(q, x, y);
    solver.assert_const(q, 0xF, 4);
    assert!(is_sat(&solver.check().expect("check")));
}

/// `bvurem x 0 = x`.
#[test]
fn urem_by_zero_is_dividend() {
    let mut solver = BvSolver::new();
    let (x, y, rem) = (TermId::new(1), TermId::new(2), TermId::new(3));
    solver.new_bv(x, 4);
    solver.new_bv(y, 4);
    solver.assert_const(x, 5, 4);
    solver.assert_const(y, 0, 4);
    solver.bv_urem(rem, x, y);
    solver.assert_const(rem, 5, 4);
    assert!(is_sat(&solver.check().expect("check")));
}

/// Signed division sanity across the no-wrap fix: `bvsdiv -6 3 = -2` (width 4,
/// two's complement: 10 / 3 → 14).
#[test]
fn sdiv_signed_correct() {
    let mut solver = BvSolver::new();
    let (x, y, q) = (TermId::new(1), TermId::new(2), TermId::new(3));
    solver.new_bv(x, 4);
    solver.new_bv(y, 4);
    solver.assert_const(x, 0b1010, 4); // -6
    solver.assert_const(y, 3, 4);
    solver.bv_sdiv(q, x, y);
    solver.assert_const(q, 0b1110, 4); // -2
    assert!(
        is_sat(&solver.check().expect("check")),
        "-6 / 3 must equal -2"
    );
    // A wrong quotient must be rejected.
    let mut solver2 = BvSolver::new();
    let (x2, y2, q2) = (TermId::new(1), TermId::new(2), TermId::new(3));
    solver2.new_bv(x2, 4);
    solver2.new_bv(y2, 4);
    solver2.assert_const(x2, 0b1010, 4);
    solver2.assert_const(y2, 3, 4);
    solver2.bv_sdiv(q2, x2, y2);
    solver2.assert_const(q2, 0b0011, 4); // +3, wrong
    assert!(is_unsat(&solver2.check().expect("check")));
}

/// Signed remainder sanity: `bvsrem -6 3 = 0` (width 4), sign of dividend.
#[test]
fn srem_signed_correct() {
    let mut solver = BvSolver::new();
    let (x, y, rem) = (TermId::new(1), TermId::new(2), TermId::new(3));
    solver.new_bv(x, 4);
    solver.new_bv(y, 4);
    solver.assert_const(x, 0b1010, 4); // -6
    solver.assert_const(y, 3, 4);
    solver.bv_srem(rem, x, y);
    solver.assert_const(rem, 0, 4);
    assert!(
        is_sat(&solver.check().expect("check")),
        "-6 % 3 must equal 0"
    );
}
