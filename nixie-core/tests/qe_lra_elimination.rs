//! Equivalence regression tests for the linear real-arithmetic quantifier
//! eliminators (`FerranteRackoffEliminator`, `VirtualTermEliminator`) and the
//! `eliminate_linear` dispatcher.
//!
//! Each test fixes a quantifier-free matrix `φ(x, y)` with a single real
//! quantified variable `x` and a single real free variable `y`, states the
//! hand-derived quantifier-free equivalent `ψ(y)` of `∃x. φ`, and checks that
//! **both** eliminators produce a formula logically equivalent to `ψ` – by
//! evaluating the eliminated formula and `ψ` at a dense grid of `y` values
//! (quarter steps over `[-10, 10]`, which straddles every integer breakpoint of
//! these fixtures) and asserting they agree at every point. A `false success`
//! (an eliminator that returns the body unchanged with `x` still free) would
//! disagree with `ψ`, so it cannot pass.

use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::interner::Spur;
use nixie_core::qe::arith::{
    FerranteRackoffEliminator, LinearElimResult, VirtualTermEliminator, eliminate_linear,
};
use num_rational::Rational64;

fn real_var(tm: &mut TermManager, name: &str) -> TermId {
    let real_sort = tm.sorts.real_sort;
    tm.mk_var(name, real_sort)
}

fn rl(tm: &mut TermManager, n: i64) -> TermId {
    tm.mk_real(Rational64::new(n, 1))
}

/// Exact-rational evaluator interpreting the single free variable `y` (named by
/// `y_spur`) as `y_val`; every other variable is a bug (it should have been
/// eliminated).
fn eval_bool(tm: &TermManager, id: TermId, y_spur: Spur, y_val: Rational64) -> bool {
    fn num(tm: &TermManager, id: TermId, y_spur: Spur, y_val: Rational64) -> Rational64 {
        match &tm.get(id).expect("term").kind {
            TermKind::Var(s) => {
                assert_eq!(*s, y_spur, "unexpected free variable in eliminated formula");
                y_val
            }
            TermKind::IntConst(n) => {
                let v: i64 = n.try_into().expect("int const fits i64");
                Rational64::new(v, 1)
            }
            TermKind::RealConst(r) => *r,
            TermKind::Neg(a) => -num(tm, *a, y_spur, y_val),
            TermKind::Add(args) => args.iter().fold(Rational64::new(0, 1), |acc, &a| {
                acc + num(tm, a, y_spur, y_val)
            }),
            TermKind::Sub(a, b) => num(tm, *a, y_spur, y_val) - num(tm, *b, y_spur, y_val),
            TermKind::Mul(args) => args.iter().fold(Rational64::new(1, 1), |acc, &a| {
                acc * num(tm, a, y_spur, y_val)
            }),
            TermKind::Div(a, b) => num(tm, *a, y_spur, y_val) / num(tm, *b, y_spur, y_val),
            other => panic!("unexpected arithmetic term {other:?}"),
        }
    }
    match &tm.get(id).expect("term").kind {
        TermKind::True => true,
        TermKind::False => false,
        TermKind::Not(a) => !eval_bool(tm, *a, y_spur, y_val),
        TermKind::And(args) => args.iter().all(|&a| eval_bool(tm, a, y_spur, y_val)),
        TermKind::Or(args) => args.iter().any(|&a| eval_bool(tm, a, y_spur, y_val)),
        TermKind::Implies(a, b) => {
            !eval_bool(tm, *a, y_spur, y_val) || eval_bool(tm, *b, y_spur, y_val)
        }
        TermKind::Xor(a, b) => eval_bool(tm, *a, y_spur, y_val) != eval_bool(tm, *b, y_spur, y_val),
        TermKind::Ite(c, t, e) => {
            if eval_bool(tm, *c, y_spur, y_val) {
                eval_bool(tm, *t, y_spur, y_val)
            } else {
                eval_bool(tm, *e, y_spur, y_val)
            }
        }
        TermKind::Lt(a, b) => num(tm, *a, y_spur, y_val) < num(tm, *b, y_spur, y_val),
        TermKind::Le(a, b) => num(tm, *a, y_spur, y_val) <= num(tm, *b, y_spur, y_val),
        TermKind::Gt(a, b) => num(tm, *a, y_spur, y_val) > num(tm, *b, y_spur, y_val),
        TermKind::Ge(a, b) => num(tm, *a, y_spur, y_val) >= num(tm, *b, y_spur, y_val),
        TermKind::Eq(a, b) => num(tm, *a, y_spur, y_val) == num(tm, *b, y_spur, y_val),
        other => panic!("unexpected boolean term {other:?}"),
    }
}

/// Assert that `result` is logically equivalent to `expected` (both `x`-free,
/// possibly mentioning `y`) over the dense quarter-step `y` grid.
fn assert_equiv_over_grid(tm: &TermManager, result: TermId, expected: TermId, y_spur: Spur) {
    for k in -40..=40 {
        let val = Rational64::new(k, 4);
        let got = eval_bool(tm, result, y_spur, val);
        let want = eval_bool(tm, expected, y_spur, val);
        assert_eq!(
            got, want,
            "disagreement at y = {val}: eliminated = {got}, expected = {want}"
        );
    }
}

/// The eliminated variable must be syntactically absent from `id`.
fn x_free(tm: &TermManager, id: TermId, x: Spur) -> bool {
    let Some(term) = tm.get(id) else {
        return true;
    };
    if let TermKind::Var(s) = term.kind {
        return s != x;
    }
    nixie_core::ast::traversal::get_children(&term.kind)
        .iter()
        .all(|&c| x_free(tm, c, x))
}

/// Run both eliminators on `∃x. φ` and assert each result equals `expected(y)`.
fn check_both(
    build: impl Fn(&mut TermManager, TermId, TermId) -> TermId,
    expected_build: impl Fn(&mut TermManager, TermId) -> TermId,
) {
    // Ferrante–Rackoff.
    {
        let mut tm = TermManager::new();
        let x = real_var(&mut tm, "x");
        let y = real_var(&mut tm, "y");
        let phi = build(&mut tm, x, y);
        let mut e = FerranteRackoffEliminator::new();
        let result = e
            .eliminate_exists("x".to_string(), phi, &mut tm)
            .expect("FR elimination should succeed");
        let x_spur = tm.intern_str("x");
        assert!(x_free(&tm, result, x_spur), "FR left x free");
        let expected = expected_build(&mut tm, y);
        let y_spur = tm.intern_str("y");
        assert_equiv_over_grid(&tm, result, expected, y_spur);
    }
    // Loos–Weispfenning virtual substitution.
    {
        let mut tm = TermManager::new();
        let x = real_var(&mut tm, "x");
        let y = real_var(&mut tm, "y");
        let phi = build(&mut tm, x, y);
        let mut e = VirtualTermEliminator::new();
        let result = e
            .eliminate_exists("x".to_string(), phi, &mut tm)
            .expect("VT elimination should succeed");
        let x_spur = tm.intern_str("x");
        assert!(x_free(&tm, result, x_spur), "VT left x free");
        let expected = expected_build(&mut tm, y);
        let y_spur = tm.intern_str("y");
        assert_equiv_over_grid(&tm, result, expected, y_spur);
    }
}

fn true_formula(tm: &mut TermManager, _y: TermId) -> TermId {
    tm.mk_true()
}

fn false_formula(tm: &mut TermManager, _y: TermId) -> TermId {
    tm.mk_false()
}

#[test]
fn exists_open_band_is_always_true() {
    // ∃x. (x > y) ∧ (x < y + 2)  ≡  true.
    check_both(
        |tm, x, y| {
            let c1 = tm.mk_gt(x, y);
            let two = rl(tm, 2);
            let yp2 = tm.mk_add(vec![y, two]);
            let c2 = tm.mk_lt(x, yp2);
            tm.mk_and(vec![c1, c2])
        },
        true_formula,
    );
}

#[test]
fn exists_equality_yields_residual_on_y() {
    // ∃x. (x = y) ∧ (y > 3)  ≡  (y > 3).
    check_both(
        |tm, x, y| {
            let eq = tm.mk_eq(x, y);
            let three = rl(tm, 3);
            let gt = tm.mk_gt(y, three);
            tm.mk_and(vec![eq, gt])
        },
        |tm, y| {
            let three = rl(tm, 3);
            tm.mk_gt(y, three)
        },
    );
}

#[test]
fn exists_scaled_equality_is_true() {
    // ∃x. (2x ≤ y) ∧ (2x ≥ y)  ≡  ∃x. 2x = y  ≡  true (x = y/2).
    check_both(
        |tm, x, y| {
            let two = rl(tm, 2);
            let two_x = tm.mk_mul(vec![two, x]);
            let c1 = tm.mk_le(two_x, y);
            let two2 = rl(tm, 2);
            let two_x2 = tm.mk_mul(vec![two2, x]);
            let c2 = tm.mk_ge(two_x2, y);
            tm.mk_and(vec![c1, c2])
        },
        true_formula,
    );
}

#[test]
fn exists_reversed_bounds_is_false() {
    // ∃x. (x ≥ y) ∧ (x ≤ y - 1)  ≡  false.
    check_both(
        |tm, x, y| {
            let c1 = tm.mk_ge(x, y);
            let one = rl(tm, 1);
            let ym1 = tm.mk_sub(y, one);
            let c2 = tm.mk_le(x, ym1);
            tm.mk_and(vec![c1, c2])
        },
        false_formula,
    );
}

#[test]
fn exists_single_upper_bound_is_true() {
    // ∃x. x < y  ≡  true (unbounded below).
    check_both(|tm, x, y| tm.mk_lt(x, y), true_formula);
}

#[test]
fn exists_disequality_is_true() {
    // ∃x. x ≠ y  ≡  true over the reals.
    check_both(
        |tm, x, y| {
            let eq = tm.mk_eq(x, y);
            tm.mk_not(eq)
        },
        true_formula,
    );
}

#[test]
fn exists_contradictory_strict_bounds_is_false() {
    // ∃x. (x > y) ∧ (x < y)  ≡  false.
    check_both(
        |tm, x, y| {
            let c1 = tm.mk_gt(x, y);
            let c2 = tm.mk_lt(x, y);
            tm.mk_and(vec![c1, c2])
        },
        false_formula,
    );
}

#[test]
fn exists_closed_interval_from_zero_to_y() {
    // ∃x. (x ≥ 0) ∧ (x ≤ y)  ≡  (y ≥ 0).
    check_both(
        |tm, x, y| {
            let zero = rl(tm, 0);
            let c1 = tm.mk_ge(x, zero);
            let c2 = tm.mk_le(x, y);
            tm.mk_and(vec![c1, c2])
        },
        |tm, y| {
            let zero = rl(tm, 0);
            tm.mk_ge(y, zero)
        },
    );
}

#[test]
fn exists_open_interval_from_zero_to_y() {
    // ∃x. (x > 0) ∧ (x < y)  ≡  (y > 0).
    check_both(
        |tm, x, y| {
            let zero = rl(tm, 0);
            let c1 = tm.mk_gt(x, zero);
            let c2 = tm.mk_lt(x, y);
            tm.mk_and(vec![c1, c2])
        },
        |tm, y| {
            let zero = rl(tm, 0);
            tm.mk_gt(y, zero)
        },
    );
}

#[test]
fn exists_negated_conjunction_via_de_morgan() {
    // ∃x. ¬((x ≤ y) ∧ (x ≥ y + 1))  – the inner conjunction is unsatisfiable in
    // x for every y, so its negation holds for some x ≡ true.
    check_both(
        |tm, x, y| {
            let c1 = tm.mk_le(x, y);
            let one = rl(tm, 1);
            let yp1 = tm.mk_add(vec![y, one]);
            let c2 = tm.mk_ge(x, yp1);
            let conj = tm.mk_and(vec![c1, c2]);
            tm.mk_not(conj)
        },
        true_formula,
    );
}

#[test]
fn eliminate_linear_real_matches_virtual_substitution() {
    // eliminate_linear on a real variable dispatches to virtual substitution.
    // ∃x. (x > 0) ∧ (x < y)  ≡  (y > 0).
    let mut tm = TermManager::new();
    let x = real_var(&mut tm, "x");
    let y = real_var(&mut tm, "y");
    let zero = rl(&mut tm, 0);
    let c1 = tm.mk_gt(x, zero);
    let c2 = tm.mk_lt(x, y);
    let phi = tm.mk_and(vec![c1, c2]);

    let result = eliminate_linear(x, phi, &mut tm);
    assert!(result.is_eliminated());
    let term = result.term();
    let x_spur = tm.intern_str("x");
    assert!(x_free(&tm, term, x_spur));

    let zero2 = rl(&mut tm, 0);
    let expected = tm.mk_gt(y, zero2);
    let y_spur = tm.intern_str("y");
    assert_equiv_over_grid(&tm, term, expected, y_spur);
}

#[test]
fn eliminate_linear_not_applied_keeps_variable() {
    // A non-linear occurrence is reported honestly, not faked.
    let mut tm = TermManager::new();
    let x = real_var(&mut tm, "x");
    let y = real_var(&mut tm, "y");
    let xx = tm.mk_mul(vec![x, x]);
    let phi = tm.mk_eq(xx, y);

    let result = eliminate_linear(x, phi, &mut tm);
    assert!(matches!(result, LinearElimResult::NotApplied(_)));
    assert_eq!(result.term(), phi);
}
