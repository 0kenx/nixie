//! Constant-distance shift wiring (`NIXIE_BV_SHIFT_WIRING=1`): term-level
//! concat/extract rewrites of `bvshl`/`bvlshr` by a constant (Z3
//! `mk_bv_shl`/`mk_bv_lshr` numeral cases).
//!
//! `x << k = concat(x[w-1-k:0], 0^k)` and `x >>u k = concat(0^k, x[w-1:k])`
//! for `0 < k < w`.  The wiring makes shift-heavy identities converge
//! *syntactically* under the simplify cascade (the `bitrev` family:
//! 1.5–2× faster at every width, measured), at the price of concat-spine
//! terms — hence off by default pending the 509-file screen.
//!
//! Every case is the unsat/sat pair: negated identity must refute, the
//! positive must hold.

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

fn pair(width: u32, lhs: &str, rhs: &str) -> (SolverResult, SolverResult) {
    let mk = |neg: bool| {
        let body = format!("(= {lhs} {rhs})");
        let assertion = if neg { format!("(not {body})") } else { body };
        format!(
            "(set-logic QF_BV)\n(declare-fun x () (_ BitVec {width}))\n(assert {assertion})\n(check-sat)"
        )
    };
    (verdict(&mk(false)), verdict(&mk(true)))
}

#[test]
fn shl_const_is_concat_wiring() {
    for &(w, k) in &[
        (8u32, 3u32),
        (16, 1),
        (16, 15),
        (64, 40),
        (126, 3),
        (128, 127),
    ] {
        let rhs = format!("(concat ((_ extract {} 0) x) (_ bv0 {k}))", w - k - 1);
        let (pos, neg) = pair(w, &format!("(bvshl x (_ bv{k} {w}))"), &rhs);
        assert_eq!(pos, SolverResult::Sat, "w={w} k={k}");
        assert_eq!(neg, SolverResult::Unsat, "w={w} k={k}");
    }
}

#[test]
fn lshr_const_is_concat_wiring() {
    for &(w, k) in &[
        (8u32, 3u32),
        (16, 2),
        (32, 31),
        (64, 33),
        (126, 1),
        (128, 64),
    ] {
        let rhs = format!("(concat (_ bv0 {k}) ((_ extract {} {k}) x))", w - 1);
        let (pos, neg) = pair(w, &format!("(bvlshr x (_ bv{k} {w}))"), &rhs);
        assert_eq!(pos, SolverResult::Sat, "w={w} k={k}");
        assert_eq!(neg, SolverResult::Unsat, "w={w} k={k}");
    }
}

/// The boundary distances must keep their exact semantics: `k = 0` is the
/// identity, `k >= w` is all-zero (the wiring does not fire there; the
/// fold handles it — these pin the ends so a future off-by-one cannot
/// hide between them).
#[test]
fn shift_boundary_distances() {
    let (pos, neg) = pair(8, "(bvshl x (_ bv0 8))", "x");
    assert_eq!((pos, neg), (SolverResult::Sat, SolverResult::Unsat));
    let (pos, neg) = pair(8, "(bvshl x (_ bv8 8))", "(_ bv0 8)");
    assert_eq!((pos, neg), (SolverResult::Sat, SolverResult::Unsat));
    let (pos, neg) = pair(8, "(bvshl x (_ bv9 8))", "(_ bv0 8)");
    assert_eq!((pos, neg), (SolverResult::Sat, SolverResult::Unsat));
    let (pos, neg) = pair(8, "(bvlshr x (_ bv8 8))", "(_ bv0 8)");
    assert_eq!((pos, neg), (SolverResult::Sat, SolverResult::Unsat));
}
