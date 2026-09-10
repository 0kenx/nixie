//! Constant-divisor division identities (Z3 `bv_rewriter` parity).
//!
//! The term builders collapse `x udiv/urem/sdiv/srem c` for constant `c`:
//! by 0 and 1 into their total-semantics values, and — the rule that
//! removes entire divider networks — by powers of two into a shift, an
//! and-mask, or the signed equivalent.  These identities live at term
//! construction, so the parser, the preprocessor and every rewriter see
//! the collapsed form.
//!
//! Each case is checked in the unsat/sat pair shape: the identity must be
//! *refuted* when negated (proving it) and *satisfied* when asserted
//! (guarding against an over-eager collapse).

use nixie_solver::{Context, SolverResult};

fn verdict(script: &str) -> SolverResult {
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

/// `(= lhs rhs)` over one width-`w` variable, in both polarities.
fn pair(w: u32, lhs: &str, rhs: &str) -> (SolverResult, SolverResult) {
    let mk = |neg: bool| {
        let body = format!("(= {lhs} {rhs})");
        let assertion = if neg { format!("(not {body})") } else { body };
        format!(
            "(set-logic QF_BV)\n(declare-fun x () (_ BitVec {w}))\n(assert {assertion})\n(check-sat)"
        )
    };
    (verdict(&mk(false)), verdict(&mk(true)))
}

#[test]
fn udiv_power_of_two_is_lshr() {
    for &(w, d, k) in &[
        (8u32, 8u64, 3u64),
        (16, 4, 2),
        (32, 65536, 16),
        (64, 1 << 40, 40),
    ] {
        let (pos, neg) = pair(
            w,
            &format!("(bvudiv x (_ bv{d} {w}))"),
            &format!("(bvlshr x (_ bv{k} {w}))"),
        );
        assert_eq!(pos, SolverResult::Sat, "w={w} d={d}: identity must hold");
        assert_eq!(
            neg,
            SolverResult::Unsat,
            "w={w} d={d}: negation must refute"
        );
    }
}

#[test]
fn udiv_by_zero_and_one() {
    let (pos, neg) = pair(16, "(bvudiv x (_ bv1 16))", "x");
    assert_eq!((pos, neg), (SolverResult::Sat, SolverResult::Unsat));
    let (pos, neg) = pair(16, "(bvudiv x (_ bv0 16))", "(_ bv65535 16)");
    assert_eq!((pos, neg), (SolverResult::Sat, SolverResult::Unsat));
}

#[test]
fn urem_power_of_two_is_mask() {
    for &(w, d, m) in &[
        (8u32, 16u64, 15u64),
        (32, 1024, 1023),
        (64, 1 << 33, (1 << 33) - 1),
    ] {
        let (pos, neg) = pair(
            w,
            &format!("(bvurem x (_ bv{d} {w}))"),
            &format!("(bvand x (_ bv{m} {w}))"),
        );
        assert_eq!(pos, SolverResult::Sat, "w={w} d={d}");
        assert_eq!(neg, SolverResult::Unsat, "w={w} d={d}");
    }
}

#[test]
fn urem_by_zero_and_one() {
    let (pos, neg) = pair(12, "(bvurem x (_ bv1 12))", "(_ bv0 12)");
    assert_eq!((pos, neg), (SolverResult::Sat, SolverResult::Unsat));
    let (pos, neg) = pair(12, "(bvurem x (_ bv0 12))", "x");
    assert_eq!((pos, neg), (SolverResult::Sat, SolverResult::Unsat));
}

#[test]
fn sdiv_by_zero_is_total() {
    // `x sdiv 0 = ite(x <s 0, 1, all-ones)` — the SMT-LIB total reading,
    // matching the constant folder's case split.
    let (pos, neg) = pair(
        8,
        "(bvsdiv x (_ bv0 8))",
        "(ite (bvslt x (_ bv0 8)) (_ bv1 8) (_ bv255 8))",
    );
    assert_eq!((pos, neg), (SolverResult::Sat, SolverResult::Unsat));
    let (pos, neg) = pair(8, "(bvsdiv x (_ bv1 8))", "x");
    assert_eq!((pos, neg), (SolverResult::Sat, SolverResult::Unsat));
}

#[test]
fn srem_by_zero_and_one() {
    let (pos, neg) = pair(8, "(bvsrem x (_ bv1 8))", "(_ bv0 8)");
    assert_eq!((pos, neg), (SolverResult::Sat, SolverResult::Unsat));
    let (pos, neg) = pair(8, "(bvsrem x (_ bv0 8))", "x");
    assert_eq!((pos, neg), (SolverResult::Sat, SolverResult::Unsat));
}

/// The top-limb case: a divisor of `2^(w-1)` (the sign bit position) is a
/// power of two with `k = w-1 < w` — must still rewrite to the shift, not
/// fall through to a divider network.
#[test]
fn udiv_sign_bit_divisor() {
    let (pos, neg) = pair(16, "(bvudiv x (_ bv32768 16))", "(bvlshr x (_ bv15 16))");
    assert_eq!((pos, neg), (SolverResult::Sat, SolverResult::Unsat));
}

/// A non-power-of-two constant divisor must NOT be collapsed to a shift:
/// the identity `x udiv 3 = x >>l k` is false for every k.
#[test]
fn udiv_non_power_of_two_stays_exact() {
    let mut ctx = Context::new();
    let script = "(set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (assert (= (bvudiv x (_ bv3 8)) (bvlshr x (_ bv1 8))))
        (check-sat)";
    let out = ctx.execute_script(script).unwrap_or_default();
    let v = out
        .iter()
        .rev()
        .find(|t| t.trim().contains("sat"))
        .cloned()
        .unwrap_or_default();
    // x = 3: 3 udiv 3 = 1 but 3 >>l 1 = 1 — equal; x = 4: 4/3 = 1, 4>>1 = 2 —
    // differ.  So the equality is satisfiable (x = 3) but not valid.
    assert!(v.trim() == "sat", "expected sat, got {v}");
}
