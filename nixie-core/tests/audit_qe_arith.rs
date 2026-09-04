//! Regression tests for audited defects in the arithmetic QE procedures
//! (`qe::arith::cooper` and `qe::arith::omega_test`).
//!
//! The Cooper tests validate soundness semantically: for a formula `φ(x, y)`
//! the eliminated result `ψ(y)` must satisfy `ψ(y) ⟺ (∃x. φ(x, y))`, checked
//! against a brute-force search over a bounded range of `x`.

use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::qe::arith::CooperEliminator;
use std::collections::HashMap;

#[derive(Clone, Copy, Debug)]
enum Val {
    I(i128),
    B(bool),
}

impl Val {
    fn int(self) -> i128 {
        match self {
            Val::I(n) => n,
            Val::B(b) => b as i128,
        }
    }
    fn boolean(self) -> bool {
        match self {
            Val::B(b) => b,
            Val::I(n) => n != 0,
        }
    }
}

/// Evaluate a term over the linear-integer fragment produced by Cooper.
fn eval(tm: &TermManager, id: TermId, env: &HashMap<String, i128>) -> Val {
    let term = tm.get(id).expect("term exists");
    match &term.kind {
        TermKind::True => Val::B(true),
        TermKind::False => Val::B(false),
        TermKind::IntConst(n) => Val::I(n.to_string().parse::<i128>().expect("fits i128")),
        TermKind::Var(s) => {
            let name = tm.resolve_str(*s);
            Val::I(
                *env.get(name)
                    .unwrap_or_else(|| panic!("unbound var {name}")),
            )
        }
        TermKind::Neg(a) => Val::I(-eval(tm, *a, env).int()),
        TermKind::Add(args) => Val::I(args.iter().map(|&a| eval(tm, a, env).int()).sum()),
        TermKind::Sub(a, b) => Val::I(eval(tm, *a, env).int() - eval(tm, *b, env).int()),
        TermKind::Mul(args) => Val::I(args.iter().map(|&a| eval(tm, a, env).int()).product()),
        TermKind::Mod(a, b) => {
            let av = eval(tm, *a, env).int();
            let bv = eval(tm, *b, env).int();
            Val::I(av.rem_euclid(bv))
        }
        TermKind::Div(a, b) => {
            let av = eval(tm, *a, env).int();
            let bv = eval(tm, *b, env).int();
            Val::I(av.div_euclid(bv))
        }
        TermKind::Lt(a, b) => Val::B(eval(tm, *a, env).int() < eval(tm, *b, env).int()),
        TermKind::Le(a, b) => Val::B(eval(tm, *a, env).int() <= eval(tm, *b, env).int()),
        TermKind::Gt(a, b) => Val::B(eval(tm, *a, env).int() > eval(tm, *b, env).int()),
        TermKind::Ge(a, b) => Val::B(eval(tm, *a, env).int() >= eval(tm, *b, env).int()),
        TermKind::Eq(a, b) => {
            let av = eval(tm, *a, env);
            let bv = eval(tm, *b, env);
            match (av, bv) {
                (Val::B(x), Val::B(y)) => Val::B(x == y),
                _ => Val::B(av.int() == bv.int()),
            }
        }
        TermKind::Not(a) => Val::B(!eval(tm, *a, env).boolean()),
        TermKind::And(args) => Val::B(args.iter().all(|&a| eval(tm, a, env).boolean())),
        TermKind::Or(args) => Val::B(args.iter().any(|&a| eval(tm, a, env).boolean())),
        TermKind::Ite(c, t, e) => {
            if eval(tm, *c, env).boolean() {
                eval(tm, *t, env)
            } else {
                eval(tm, *e, env)
            }
        }
        other => panic!("evaluator does not handle {other:?}"),
    }
}

fn int_var(tm: &mut TermManager, name: &str) -> TermId {
    let z = tm.mk_int(0);
    let int_sort = tm.get(z).expect("int sort").sort;
    tm.mk_var(name, int_sort)
}

/// Verify `eliminate_exists("x", build(x, y)) ⟺ ∃x∈[-R,R]. build(x, y)` for
/// every `y ∈ [-y_range, y_range]`.
fn check_equivalence<F>(build: F, y_range: i128, x_range: i128)
where
    F: Fn(&mut TermManager, TermId, TermId) -> TermId,
{
    let mut tm = TermManager::new();
    let x = int_var(&mut tm, "x");
    let y = int_var(&mut tm, "y");
    let phi = build(&mut tm, x, y);

    let mut elim = CooperEliminator::new();
    let result = elim
        .eliminate_exists("x".to_string(), phi, &mut tm)
        .expect("elimination should succeed");

    // The eliminated variable must be gone.
    let x_spur = tm.intern_str("x");
    assert!(
        !mentions(&tm, result, x_spur),
        "eliminated variable still present in the result"
    );

    for yv in -y_range..=y_range {
        // Brute-force ∃x over the bounded range.
        let mut brute = false;
        for xv in -x_range..=x_range {
            let mut env = HashMap::new();
            env.insert("x".to_string(), xv);
            env.insert("y".to_string(), yv);
            if eval(&tm, phi, &env).boolean() {
                brute = true;
                break;
            }
        }
        let mut env = HashMap::new();
        env.insert("y".to_string(), yv);
        let qe = eval(&tm, result, &env).boolean();
        assert_eq!(qe, brute, "mismatch at y={yv}: qe={qe} brute={brute}");
    }
}

fn mentions(tm: &TermManager, id: TermId, x_spur: nixie_core::interner::Spur) -> bool {
    let term = tm.get(id).expect("term");
    if let TermKind::Var(s) = term.kind {
        return s == x_spur;
    }
    nixie_core::ast::traversal::get_children(&term.kind)
        .iter()
        .any(|&c| mentions(tm, c, x_spur))
}

#[test]
fn cooper_even_predicate() {
    // ∃x. 2x = y  ⟺  y even
    check_equivalence(
        |tm, x, y| {
            let two = tm.mk_int(2);
            let two_x = tm.mk_mul(vec![two, x]);
            tm.mk_eq(two_x, y)
        },
        20,
        40,
    );
}

#[test]
fn cooper_divisibility_and_bound() {
    // ∃x. (3x = y) ⟺ y divisible by 3
    check_equivalence(
        |tm, x, y| {
            let three = tm.mk_int(3);
            let three_x = tm.mk_mul(vec![three, x]);
            tm.mk_eq(three_x, y)
        },
        30,
        60,
    );
}

#[test]
fn cooper_range_constraint() {
    // ∃x. (y < x) ∧ (x < y + 3)  ⟺  true (there is always an integer strictly
    // between y and y+3, e.g. y+1).
    check_equivalence(
        |tm, x, y| {
            let lower = tm.mk_lt(y, x);
            let three = tm.mk_int(3);
            let yp3 = tm.mk_add(vec![y, three]);
            let upper = tm.mk_lt(x, yp3);
            tm.mk_and(vec![lower, upper])
        },
        20,
        60,
    );
}

#[test]
fn cooper_conjunction_of_bounds() {
    // ∃x. (x ≥ y) ∧ (2x ≤ y + 4)
    check_equivalence(
        |tm, x, y| {
            let ge = tm.mk_ge(x, y);
            let two = tm.mk_int(2);
            let two_x = tm.mk_mul(vec![two, x]);
            let four = tm.mk_int(4);
            let yp4 = tm.mk_add(vec![y, four]);
            let le = tm.mk_le(two_x, yp4);
            tm.mk_and(vec![ge, le])
        },
        25,
        80,
    );
}

#[test]
fn cooper_disjunction_and_negation() {
    // ∃x. ¬((x < y) ∨ (x > y + 2))  ≡  ∃x. (x ≥ y) ∧ (x ≤ y+2)  ⟺ true.
    check_equivalence(
        |tm, x, y| {
            let lt = tm.mk_lt(x, y);
            let two = tm.mk_int(2);
            let yp2 = tm.mk_add(vec![y, two]);
            let gt = tm.mk_gt(x, yp2);
            let or = tm.mk_or(vec![lt, gt]);
            tm.mk_not(or)
        },
        20,
        60,
    );
}

#[test]
fn cooper_rejects_nonlinear() {
    // ∃x. x*x = y is outside the linear fragment; it must be surfaced as an
    // error, never as a fabricated (or unchanged) result.
    let mut tm = TermManager::new();
    let x = int_var(&mut tm, "x");
    let y = int_var(&mut tm, "y");
    let xx = tm.mk_mul(vec![x, x]);
    let phi = tm.mk_eq(xx, y);

    let mut elim = CooperEliminator::new();
    assert!(
        elim.eliminate_exists("x".to_string(), phi, &mut tm)
            .is_err()
    );
}
