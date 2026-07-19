//! Regression tests for audited defects in `TermManager` substitution and
//! hash-cons interning.
//!
//! Finding 1 (query.rs): `substitute` used to silently drop every term kind it
//! did not special-case (`Apply`, all `Bv*`/`Str*`/`Fp*`, `Xor`, `Distinct`,
//! `Div`/`Mod`, quantifiers, `Let`), returning the term unchanged. Solved
//! equations were therefore dropped while their occurrences remained, producing
//! wrong sat/unsat answers and wrong models.
//!
//! Finding 2 (mod.rs): the hash-cons cache keyed on `TermKind` alone, so two
//! same-named variables of different sorts aliased to the first interned sort.

use oxiz_core::ast::SubstitutionBuilder;
use oxiz_core::{TermKind, TermManager};

// ===================== Finding 2: sort-aware interning =====================

#[test]
fn same_name_different_sort_do_not_alias() {
    let mut m = TermManager::new();
    let int_sort = m.sorts.int_sort;
    let real_sort = m.sorts.real_sort;

    let x_int = m.mk_var("x", int_sort);
    let x_real = m.mk_var("x", real_sort);

    assert_ne!(
        x_int, x_real,
        "same-named vars of different sorts must be distinct terms"
    );
    assert_eq!(m.get(x_int).expect("x_int").sort, int_sort);
    assert_eq!(m.get(x_real).expect("x_real").sort, real_sort);

    // Re-interning must still be idempotent per (name, sort).
    assert_eq!(m.mk_var("x", int_sort), x_int);
    assert_eq!(m.mk_var("x", real_sort), x_real);
}

// ===================== Finding 1: full-coverage substitution ================

#[test]
fn substitute_into_uninterpreted_application() {
    let mut m = TermManager::new();
    let int_sort = m.sorts.int_sort;
    let x = m.mk_var("x", int_sort);
    let fx = m.mk_apply("f", [x], int_sort);
    let three = m.mk_int(3);

    let mut sb = SubstitutionBuilder::new();
    sb.add(x, three);
    let result = sb.apply(fx, &mut m);

    assert_ne!(result, fx, "f(x) with x:=3 must not be returned unchanged");
    match &m.get(result).expect("result term").kind {
        TermKind::Apply { args, .. } => {
            assert_eq!(args.as_slice(), &[three], "expected f(3)");
        }
        other => panic!("expected Apply, got {other:?}"),
    }
}

#[test]
fn substitute_into_bitvector_term() {
    let mut m = TermManager::new();
    let bv8 = m.sorts.bitvec(8);
    let bx = m.mk_var("bx", bv8);
    let by = m.mk_var("by", bv8);
    let sum = m.mk_bv_add(bx, by);
    let five = m.mk_bitvec(5i64, 8);

    let mut sb = SubstitutionBuilder::new();
    sb.add(bx, five);
    let result = sb.apply(sum, &mut m);

    assert_ne!(result, sum, "bvadd(bx, by) with bx:=5 must change");
    match m.get(result).expect("result term").kind {
        TermKind::BvAdd(a, b) => {
            assert!(
                (a == five && b == by) || (a == by && b == five),
                "expected BvAdd operands {{five, by}} in either order, got ({a:?}, {b:?})"
            );
        }
        ref other => panic!("expected BvAdd, got {other:?}"),
    }
}

#[test]
fn substitute_into_string_term() {
    let mut m = TermManager::new();
    let string_sort = m.sorts.string_sort();
    let s = m.mk_var("s", string_sort);
    let suffix = m.mk_string_lit("!");
    let concat = m.mk_str_concat(s, suffix);
    let hello = m.mk_string_lit("hello");

    let mut sb = SubstitutionBuilder::new();
    sb.add(s, hello);
    let result = sb.apply(concat, &mut m);

    assert_ne!(result, concat, "str.++ with s:=\"hello\" must change");
    match m.get(result).expect("result term").kind {
        TermKind::StrConcat(a, b) => {
            assert_eq!(a, hello);
            assert_eq!(b, suffix);
        }
        ref other => panic!("expected StrConcat, got {other:?}"),
    }
}

#[test]
fn substitute_into_distinct_and_div() {
    let mut m = TermManager::new();
    let int_sort = m.sorts.int_sort;
    let x = m.mk_var("x", int_sort);
    let y = m.mk_var("y", int_sort);
    let z = m.mk_var("z", int_sort);
    let w = m.mk_var("w", int_sort);

    let distinct = m.mk_distinct([x, y, z]);
    let div = m.mk_div(x, y);

    let mut sb = SubstitutionBuilder::new();
    sb.add(x, w);

    let d_result = sb.apply(distinct, &mut m);
    match &m.get(d_result).expect("distinct result").kind {
        TermKind::Distinct(args) => assert_eq!(args.as_slice(), &[w, y, z]),
        other => panic!("expected Distinct, got {other:?}"),
    }

    let div_result = sb.apply(div, &mut m);
    match m.get(div_result).expect("div result").kind {
        TermKind::Div(a, b) => {
            assert_eq!(a, w);
            assert_eq!(b, y);
        }
        ref other => panic!("expected Div, got {other:?}"),
    }
}

// ===================== Finding 1: binder handling ===========================

#[test]
fn substitute_does_not_touch_shadowed_bound_variable() {
    let mut m = TermManager::new();
    let int_sort = m.sorts.int_sort;
    let x = m.mk_var("x", int_sort);
    let zero = m.mk_int(0);
    let body = m.mk_gt(x, zero); // x > 0
    let forall = m.mk_forall([("x", int_sort)], body);

    // x is bound; substituting x:=42 must leave the quantifier untouched.
    let forty_two = m.mk_int(42);
    let mut sb = SubstitutionBuilder::new();
    sb.add(x, forty_two);
    let result = sb.apply(forall, &mut m);

    assert_eq!(
        result, forall,
        "substituting a bound variable must not alter the quantifier"
    );
}

#[test]
fn substitute_is_capture_avoiding_in_quantifier() {
    let mut m = TermManager::new();
    let int_sort = m.sorts.int_sort;
    let x = m.mk_var("x", int_sort);
    let y = m.mk_var("y", int_sort);
    let body = m.mk_eq(x, y); // x = y, with x bound below
    let forall = m.mk_forall([("x", int_sort)], body);

    // Substitute y := x. Because the replacement's free variable `x` collides
    // with the bound `x`, the binder must be alpha-renamed rather than capture.
    let mut sb = SubstitutionBuilder::new();
    sb.add(y, x);
    let result = sb.apply(forall, &mut m);

    let (fresh_name, new_body) = match &m.get(result).expect("result term").kind {
        TermKind::Forall { vars, body, .. } => {
            assert_eq!(vars.len(), 1);
            (vars[0].0, *body)
        }
        other => panic!("expected Forall, got {other:?}"),
    };
    assert_ne!(
        m.resolve_str(fresh_name),
        "x",
        "bound variable must be renamed to avoid capturing the free x"
    );

    // The renamed body must be (fresh = x): one operand is the free x, the
    // other is the freshly renamed bound variable (never the original x==x).
    let fresh_str = m.resolve_str(fresh_name).to_string();
    let fresh_var = m.mk_var(&fresh_str, int_sort);
    match m.get(new_body).expect("body").kind {
        TermKind::Eq(a, b) => {
            let operands = [a, b];
            assert!(operands.contains(&x), "free x must remain in the body");
            assert!(
                operands.contains(&fresh_var),
                "renamed bound var must appear in the body"
            );
            assert_ne!(a, b, "must not collapse to x = x (capture)");
        }
        ref other => panic!("expected Eq, got {other:?}"),
    }
}

#[test]
fn substitute_passes_through_let_body() {
    let mut m = TermManager::new();
    let int_sort = m.sorts.int_sort;
    let x = m.mk_var("x", int_sort);
    let z = m.mk_var("z", int_sort);
    let five = m.mk_int(5);
    let sum = m.mk_add([x, z]); // x + z
    let let_term = m.mk_let([("z", five)], sum); // let z = 5 in (x + z)

    let ten = m.mk_int(10);
    let mut sb = SubstitutionBuilder::new();
    sb.add(x, ten);
    let result = sb.apply(let_term, &mut m);

    assert_ne!(result, let_term, "let body substitution must apply to x");
    match &m.get(result).expect("let result").kind {
        TermKind::Let { bindings, body } => {
            assert_eq!(bindings.len(), 1);
            assert_eq!(bindings[0].1, five, "binding value unchanged");
            match &m.get(*body).expect("let body").kind {
                TermKind::Add(args) => assert_eq!(args.as_slice(), &[ten, z]),
                other => panic!("expected Add body, got {other:?}"),
            }
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn substitute_shadowed_let_variable_is_noop() {
    let mut m = TermManager::new();
    let int_sort = m.sorts.int_sort;
    let z = m.mk_var("z", int_sort);
    let five = m.mk_int(5);
    let body = m.mk_add([z, five]); // z + 5
    let let_term = m.mk_let([("z", five)], body); // let z = 5 in (z + 5)

    // z is let-bound in the body; substituting z:=99 must be a no-op.
    let ninety_nine = m.mk_int(99);
    let mut sb = SubstitutionBuilder::new();
    sb.add(z, ninety_nine);
    let result = sb.apply(let_term, &mut m);

    assert_eq!(result, let_term, "let-bound z must be shadowed");
}
