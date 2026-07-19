//! Regression tests for audited defects in package `core-p3`:
//!
//!   1. `ast/manager/builder.rs`: `mk_bv_extract` computed
//!      `high - low + 1` with unvalidated indices, underflowing (panic in
//!      debug, ~4-billion-bit sort in release) on e.g. `low > high`.
//!   2. `ast/validation.rs`: `eval_term`/`eval_term_internal`'s `BvNot` mask
//!      computed `(1u64 << width) - 1` unguarded for `width >= 64` (panic in
//!      debug, wrong mask of `0` in release).
//!   3. `smtlib/parser/commands.rs`: `set-info` only accepted
//!      `StringLit`/`Symbol` values, so the near-universal
//!      `(set-info :smt-lib-version 2.6)` header aborted parsing of the
//!      *entire* script (numerals/decimals lex differently and `parse_script`
//!      parses eagerly).
//!   4. `smtlib/parser/commands.rs`: `define-sort` bodies were restricted to
//!      a bare symbol, so compound bodies like `(Array Int Int)` were a hard
//!      parse error; parametric aliases (arity > 0) were accepted but later
//!      silently resolved to an unrelated fresh `Uninterpreted` sort with no
//!      diagnostic.
//!   5. `tactic/mbp.rs`: `is_linear_real`/`is_linear_int` always returned
//!      `true`, so nonlinear literals (e.g. `x * y <= 5`) were run through
//!      the bare-variable Fourier-Motzkin-style projector, which silently
//!      dropped the eliminated variable's occurrence while still reporting
//!      it as eliminated -- fabricating an unsound projection.
//!
//! Also covers two deferred hardening items applied alongside the above:
//!   - `ast/manager/query.rs`: `TermManager::simplify`/`substitute` now cap
//!     recursion depth (mirroring `rewrite/combined.rs`'s `RewriteContext`),
//!     returning the term unchanged on a pathologically deep input instead
//!     of overflowing the stack.
//!   - `tactic/mod.rs`: `ManagedTactic` is now re-exported from the crate's
//!     `tactic` module root.

use oxiz_core::ast::{Model, ModelValue, SubstitutionBuilder, TermManager, eval_term};
use oxiz_core::smtlib::{Command, parse_script};
use oxiz_core::tactic::mbp::{MbpEngine, Model as MbpModel};

// ===================== Finding 1: mk_bv_extract underflow ==================

#[test]
fn mk_bv_extract_with_low_greater_than_high_does_not_panic_or_explode_width() {
    let mut m = TermManager::new();
    let bv8 = m.sorts.bitvec(8);
    let x = m.mk_var("x", bv8);

    // `(_ extract 0 5)` on an 8-bit value: low(5) > high(0), which used to
    // underflow `high - low + 1` (panic in debug, ~4.29e9-bit sort in
    // release). Must neither panic nor produce a pathological width.
    let extracted = m.mk_bv_extract(0, 5, x);
    let sort_id = m.get(extracted).expect("term exists").sort;
    let width = m
        .sorts
        .get(sort_id)
        .and_then(|s| s.bitvec_width())
        .expect("bitvec sort");
    assert!(
        width < 100,
        "invalid extract indices must not produce a huge/wrapped width, got {width}"
    );
}

#[test]
fn mk_bv_extract_with_valid_indices_still_computes_correct_width() {
    let mut m = TermManager::new();
    let bv8 = m.sorts.bitvec(8);
    let x = m.mk_var("x", bv8);

    // (_ extract 5 2) on an 8-bit value: width = 5 - 2 + 1 = 4.
    let extracted = m.mk_bv_extract(5, 2, x);
    let sort_id = m.get(extracted).expect("term exists").sort;
    let width = m
        .sorts
        .get(sort_id)
        .and_then(|s| s.bitvec_width())
        .expect("bitvec sort");
    assert_eq!(width, 4, "valid extract indices must be unaffected");
}

// ===================== Finding 2: BvNot mask for width >= 64 ===============

#[test]
fn eval_term_bv_not_width_64_does_not_panic_and_is_correct() {
    let mut m = TermManager::new();
    let bv64 = m.sorts.bitvec(64);
    let x = m.mk_var("x", bv64);
    let not_x = m.mk_bv_not(x);

    let mut model = Model::new();
    model.assign_bitvec(x, 0u64, 64);

    // Previously `(1u64 << 64) - 1` panicked in debug builds (shift overflow)
    // and wrapped to a mask of `0` in release, corrupting the result.
    let result = eval_term(not_x, &m, &model);
    assert_eq!(
        result,
        Some(ModelValue::BitVec {
            value: u64::MAX,
            width: 64,
        }),
        "!0 over 64 bits must be all-ones, not masked to 0"
    );
}

#[test]
fn eval_term_bv_not_width_64_nonzero_value_is_correct() {
    let mut m = TermManager::new();
    let bv64 = m.sorts.bitvec(64);
    let x = m.mk_var("x", bv64);
    let not_x = m.mk_bv_not(x);

    let mut model = Model::new();
    // Top bit set; !value must flip every bit, not get masked away.
    model.assign_bitvec(x, 0x8000_0000_0000_0001u64, 64);

    let result = eval_term(not_x, &m, &model);
    assert_eq!(
        result,
        Some(ModelValue::BitVec {
            value: !0x8000_0000_0000_0001u64,
            width: 64,
        })
    );
}

#[test]
fn cached_evaluator_bv_not_width_64_does_not_panic() {
    use oxiz_core::ast::CachedEvaluator;

    let mut m = TermManager::new();
    let bv64 = m.sorts.bitvec(64);
    let x = m.mk_var("x", bv64);
    let not_x = m.mk_bv_not(x);

    let mut model = Model::new();
    model.assign_bitvec(x, 0u64, 64);

    // Exercises `eval_term_internal` (the cached path), the second unguarded
    // mask site.
    let mut evaluator = CachedEvaluator::new(&m, &model);
    let result = evaluator.eval(not_x);
    assert_eq!(
        result,
        Some(ModelValue::BitVec {
            value: u64::MAX,
            width: 64,
        })
    );
}

// ===================== Finding 3: set-info accepts any value ===============

#[test]
fn set_info_smt_lib_version_header_does_not_abort_script() {
    let mut m = TermManager::new();
    // The near-universal SMT-LIB header: `2.6` lexes as a `Decimal` token,
    // which `set-info` used to reject, aborting the whole script.
    let script = r#"
        (set-info :smt-lib-version 2.6)
        (set-info :category "crafted")
        (declare-const x Int)
        (assert (= x 1))
        (check-sat)
    "#;
    let commands = parse_script(script, &mut m).expect("script with set-info header must parse");
    assert_eq!(commands.len(), 5);
    match &commands[0] {
        Command::SetInfo(keyword, value) => {
            assert_eq!(keyword, "smt-lib-version");
            assert_eq!(value, "2.6");
        }
        other => panic!("expected SetInfo, got {other:?}"),
    }
}

#[test]
fn set_info_accepts_numeral_and_sexpr_values() {
    let mut m = TermManager::new();
    let script = r#"
        (set-info :some-numeral 42)
        (set-info :some-sexpr (foo bar (baz 1 2)))
        (check-sat)
    "#;
    let commands = parse_script(script, &mut m).expect("numeral/s-expr set-info must parse");
    match &commands[0] {
        Command::SetInfo(_, value) => assert_eq!(value, "42"),
        other => panic!("expected SetInfo, got {other:?}"),
    }
    match &commands[1] {
        Command::SetInfo(_, value) => assert_eq!(value, "(foo bar (baz 1 2))"),
        other => panic!("expected SetInfo, got {other:?}"),
    }
}

// ===================== Finding 4: define-sort =====================

#[test]
fn define_sort_compound_body_parses_and_resolves_to_the_real_sort() {
    let mut m = TermManager::new();
    // `IA` must resolve to a genuine `(Array Int Int)` sort: if it fell
    // through to a fresh, unrelated `Uninterpreted` sort (the pre-fix
    // behavior once the parse error itself is worked around), asserting
    // `f = a1` below would be a sort-mismatch error.
    let script = r#"
        (define-sort IA () (Array Int Int))
        (declare-fun f () IA)
        (declare-fun a1 () (Array Int Int))
        (assert (= f a1))
        (check-sat)
    "#;
    let commands =
        parse_script(script, &mut m).expect("compound define-sort body must parse and resolve");
    assert_eq!(commands.len(), 5);
}

#[test]
fn define_sort_simple_alias_still_works() {
    let mut m = TermManager::new();
    let script = r#"
        (define-sort MyInt () Int)
        (declare-fun f () MyInt)
        (declare-fun g () Int)
        (assert (= f g))
        (check-sat)
    "#;
    let commands = parse_script(script, &mut m).expect("bare-symbol define-sort must still work");
    assert_eq!(commands.len(), 5);
}

#[test]
fn define_sort_parametric_is_rejected_honestly_not_silently_corrupted() {
    let mut m = TermManager::new();
    // Arity > 0: this parser cannot substitute parameters at instantiation
    // sites, so accepting the definition would let later uses of `Pair`
    // silently resolve to an unrelated fresh `Uninterpreted` sort with no
    // diagnostic. It must be rejected with an explicit error instead.
    let script = r#"
        (define-sort Pair (X Y) (Array X Y))
        (declare-fun f () (Pair Int Int))
        (check-sat)
    "#;
    let result = parse_script(script, &mut m);
    assert!(
        result.is_err(),
        "parametric define-sort must fail honestly, not silently corrupt later declarations"
    );
}

// ===================== Finding 5: MBP nonlinear soundness ==================

#[test]
fn mbp_does_not_silently_eliminate_variable_through_nonlinear_literal() {
    let mut m = TermManager::new();
    let int_sort = m.sorts.int_sort;
    let x = m.mk_var("x", int_sort);
    let y = m.mk_var("y", int_sort);
    let five = m.mk_int(5);
    let xy = m.mk_mul([x, y]);
    let nonlinear_lit = m.mk_le(xy, five); // x * y <= 5

    let x_name = m.intern_str("x");
    let model = MbpModel::new();

    let mut engine = MbpEngine::new(&mut m);
    let result = engine
        .project(nonlinear_lit, &[x_name], &model)
        .expect("project must not error even when it cannot eliminate the variable");
    drop(engine);

    assert!(
        !result.eliminated.contains(&x_name),
        "a variable that only occurs in a nonlinear literal must not be reported as eliminated"
    );
    assert!(
        result.remaining.contains(&x_name),
        "the nonlinear variable must be reported as remaining (projection incomplete)"
    );

    // The projected formula must still literally contain the untouched
    // nonlinear literal (sound-but-incomplete) rather than a fabricated,
    // `x`-free formula.
    let formula = result.to_formula(&mut m);
    assert_eq!(
        formula, nonlinear_lit,
        "nonlinear literal must be passed through unchanged, not silently rewritten"
    );
}

#[test]
fn mbp_still_eliminates_genuinely_linear_variable() {
    let mut m = TermManager::new();
    let int_sort = m.sorts.int_sort;
    let x = m.mk_var("x", int_sort);
    let one = m.mk_int(1);
    let five = m.mk_int(5);
    let lb = m.mk_ge(x, one); // x >= 1
    let ub = m.mk_le(x, five); // x <= 5
    let conj = m.mk_and([lb, ub]);

    let x_name = m.intern_str("x");
    let model = MbpModel::new();

    let mut engine = MbpEngine::new(&mut m);
    let result = engine
        .project(conj, &[x_name], &model)
        .expect("project must succeed for a linear formula");
    drop(engine);

    assert!(
        result.eliminated.contains(&x_name),
        "a genuinely linear variable must still be eliminated"
    );
    assert!(!result.remaining.contains(&x_name));
}

// ===================== Deferral (a): query.rs recursion cap =================

#[test]
fn simplify_and_substitute_do_not_overflow_stack_on_deep_terms() {
    let mut m = TermManager::new();
    let int_sort = m.sorts.int_sort;
    let mut t = m.mk_var("p", int_sort);
    // Deep enough to exceed the depth cap (1000) but built iteratively, so
    // only the *traversal* (not construction) risks overflowing the stack.
    // `mk_neg` (unlike `mk_not`) does not cancel double negation, so this
    // genuinely builds a term of depth 5000 rather than collapsing back to
    // `p`.
    for _ in 0..5000 {
        t = m.mk_neg(t);
    }

    // Must return without panicking/crashing; a pathologically deep term is
    // handled by bailing out (returning the term unchanged) rather than
    // overflowing the native call stack.
    let simplified = m.simplify(t);
    assert!(m.get(simplified).is_some());

    let mut sb = SubstitutionBuilder::new();
    let substituted = sb.apply(t, &mut m);
    assert!(m.get(substituted).is_some());
}

// ===================== Deferral (b): ManagedTactic re-export ================

#[test]
fn managed_tactic_is_reexported_from_tactic_root() {
    // Compile-time check: this path must resolve without an explicit
    // `oxiz_core::tactic::registry::` prefix.
    fn _assert_path<T: ?Sized + oxiz_core::tactic::ManagedTactic>() {}
}
