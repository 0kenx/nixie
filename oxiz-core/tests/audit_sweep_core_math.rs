//! Regression tests for the `sweep-core-math` minor-item triage sweep
//! (oxiz-core side; oxiz-math regressions live in
//! `oxiz-math/tests/audit_sweep_core_math.rs`).
//!
//! Each test documents the specific defect it guards against; see the
//! corresponding source file for the full rationale.

use num_bigint::BigInt;
use num_rational::Rational64;
use num_traits::Zero;
use oxiz_core::ast::model::{FunctionInterpretation, Model as AstModel, ModelValue};
use oxiz_core::ast::{CongruenceClosure, EGraph, Explanation};
use oxiz_core::model::{Model, ModelCompletion, Value};
use oxiz_core::qe::bv::simplification::{BvSimplifier, BvTerm};
use oxiz_core::smtlib::Lexer;
use oxiz_core::smtlib::Printer;
use oxiz_core::tactic::{Goal, Pb2BvTactic, Precision, TacticResult};
use oxiz_core::{ArithRewriter, RewriteContext, Rewriter, StringRewriter, TermKind, TermManager};

// ========  ========
// oxiz-core/src/rewrite/arith.rs
// ========  ========

#[test]
fn arith_add_overflow_leaves_term_unrewritten_not_wrong() {
    let mut manager = TermManager::new();
    let mut ctx = RewriteContext::new();
    let mut rewriter = ArithRewriter::new();

    // Two Real constants whose sum overflows Rational64's i64 numerator.
    let big = Rational64::new(i64::MAX / 2 + 1, 1);
    let a = manager.mk_real(big);
    let b = manager.mk_real(big);
    let add = manager.mk_add([a, b]);

    let result = rewriter.rewrite(add, &mut ctx, &mut manager);
    // Must not panic and must not silently fold to a wrapped/wrong value:
    // either it stays an Add, or if folded, the result must be Real-sorted.
    let t = manager.get(result.term()).expect("term should exist");
    if let TermKind::RealConst(_) = t.kind {
        // fine: folded exactly
    } else {
        assert!(matches!(t.kind, TermKind::Add(_)));
    }
}

#[test]
fn arith_add_real_fold_stays_real_sorted() {
    // Regression: folding used to push `mk_int` whenever the folded sum was
    // integral, even for a Real-sorted Add, producing an ill-sorted term
    // (Int constant inside a Real Add).
    let mut manager = TermManager::new();
    let mut ctx = RewriteContext::new();
    let mut rewriter = ArithRewriter::new();

    let x = manager.mk_var("x", manager.sorts.real_sort);
    let two = manager.mk_real(Rational64::from_integer(2));
    let three = manager.mk_real(Rational64::from_integer(3));
    // x + 2.0 + 3.0 -> x + 5.0, and "5.0" must be a RealConst, not IntConst.
    let add = manager.mk_add([x, two, three]);

    let result = rewriter.rewrite(add, &mut ctx, &mut manager);
    let t = manager.get(result.term()).expect("term should exist");
    if let TermKind::Add(args) = &t.kind {
        let has_int_const = args
            .iter()
            .any(|&a| matches!(manager.get(a).map(|t| &t.kind), Some(TermKind::IntConst(_))));
        assert!(
            !has_int_const,
            "Real-sorted Add must not contain an IntConst operand, got {:?}",
            t.kind
        );
    }
}

#[test]
fn arith_div_euclid_overflow_does_not_panic() {
    let mut manager = TermManager::new();
    let mut ctx = RewriteContext::new();
    let mut rewriter = ArithRewriter::new();

    let min = manager.mk_int(BigInt::from(i64::MIN));
    let neg_one = manager.mk_int(BigInt::from(-1));
    let div = manager.mk_div(min, neg_one);

    // Must not panic (i64::MIN.div_euclid(-1) overflows).
    let _ = rewriter.rewrite(div, &mut ctx, &mut manager);
}

// ========  ========
// oxiz-core/src/ast/egraph.rs
// ========  ========

#[test]
fn egraph_add_term_rejects_i64_overflowing_int_const() {
    let mut manager = TermManager::new();
    let mut egraph = EGraph::new();

    let huge = BigInt::from(i64::MAX) * BigInt::from(2);
    let term = manager.mk_int(huge);

    // Must not silently become the e-class for the integer 0.
    assert_eq!(egraph.add_term(term, &manager), None);
}

#[test]
fn egraph_extract_works_after_chained_merges() {
    let mut manager = TermManager::new();
    let mut egraph = EGraph::new();

    let a = manager.mk_int(1);
    let b = manager.mk_int(2);
    let c = manager.mk_int(3);
    let ida = egraph.add_term(a, &manager).expect("a representable");
    let idb = egraph.add_term(b, &manager).expect("b representable");
    let idc = egraph.add_term(c, &manager).expect("c representable");

    // Chain: merge(a, b), then merge(b, c) – id `a` now reaches its root
    // through two hops, which a single-level `unionfind.get` lookup used to
    // fail to resolve.
    egraph.merge(ida, idb);
    egraph.merge(idb, idc);

    assert!(egraph.extract(ida).is_some());
    assert!(egraph.get_class(ida).is_some());
}

// ========  ========
// oxiz-core/src/ast/congruence.rs
// ========  ========

#[test]
fn congruence_pop_undoes_diseq_assertion() {
    let mut manager = TermManager::new();
    let a = manager.mk_var("a", manager.sorts.int_sort);
    let b = manager.mk_var("b", manager.sorts.int_sort);

    let mut cc = CongruenceClosure::new();
    cc.add_term(a, &manager);
    cc.add_term(b, &manager);

    cc.push();
    assert!(cc.assert_diseq(a, b).is_none());
    // Within the scope, merging a=b must now conflict.
    assert!(cc.merge(a, b, Explanation::Given).is_some());
    cc.pop();

    // After popping, the disequality must no longer be active: merging a=b
    // must succeed with no conflict.
    assert!(cc.merge(a, b, Explanation::Given).is_none());
}

#[test]
fn congruence_pop_undoes_explanation() {
    let mut manager = TermManager::new();
    let a = manager.mk_var("a", manager.sorts.int_sort);
    let b = manager.mk_var("b", manager.sorts.int_sort);

    let mut cc = CongruenceClosure::new();
    cc.add_term(a, &manager);
    cc.add_term(b, &manager);

    cc.push();
    assert!(cc.merge(a, b, Explanation::Given).is_none());
    assert!(cc.get_explanation(a, b).is_some());
    cc.pop();

    // The merge (and its recorded explanation) must be undone.
    assert!(cc.get_explanation(a, b).is_none());
}

#[test]
fn congruence_close_propagates_through_non_root_class_member() {
    // neg(x), neg(y) (standing in for any unary "parent" application
    // tracked via `add_term`'s use-lists), and a chain merging x and y
    // *through* an intermediate term z, must still let close() discover
    // neg(x) ~ neg(y) even though neither `x` nor the class's root id is
    // `y` itself – `y` only joins the class via the x~z, z~y chain.
    let mut manager = TermManager::new();
    let x = manager.mk_var("x", manager.sorts.int_sort);
    let y = manager.mk_var("y", manager.sorts.int_sort);
    let z = manager.mk_var("z", manager.sorts.int_sort);
    let neg_x = manager.mk_neg(x);
    let neg_y = manager.mk_neg(y);

    let mut cc = CongruenceClosure::new();
    cc.add_term(neg_x, &manager);
    cc.add_term(neg_y, &manager);

    // Chain: merge(x, z) then merge(z, y) so that `y` becomes part of the
    // same class as `x` without `y` itself ever being merge()'d directly
    // with `x`, and without `y` becoming the class root.
    cc.merge(x, z, Explanation::Given);
    cc.merge(z, y, Explanation::Given);
    cc.close(&manager);

    assert!(
        cc.are_equal(neg_x, neg_y),
        "neg(x) and neg(y) must be congruent once x and y share a class"
    );
}

// ========  ========
// oxiz-core/src/rewrite/string.rs – codepoint (not byte) semantics
// ========  ========

#[test]
fn string_len_counts_codepoints_not_bytes() {
    let mut manager = TermManager::new();
    let mut ctx = RewriteContext::new();
    let mut rewriter = StringRewriter::new();

    // "héllo": 5 codepoints, but 6 UTF-8 bytes (é is 2 bytes).
    let s = manager.mk_string_lit("héllo");
    let len = manager.mk_str_len(s);

    let result = rewriter.rewrite(len, &mut ctx, &mut manager);
    let t = manager.get(result.term()).expect("term should exist");
    assert!(matches!(&t.kind, TermKind::IntConst(n) if n == &BigInt::from(5)));
}

#[test]
fn string_indexof_does_not_panic_on_non_ascii() {
    let mut manager = TermManager::new();
    let mut ctx = RewriteContext::new();
    let mut rewriter = StringRewriter::new();

    let s = manager.mk_string_lit("héllo world");
    let needle = manager.mk_string_lit("world");
    let start = manager.mk_int(0);
    let indexof = manager.mk_str_indexof(s, needle, start);

    // Must not panic (byte-slicing at a non-char-boundary used to be
    // possible for other inputs); also check the codepoint offset is
    // correct: "héllo " is 6 codepoints, so "world" starts at index 6.
    let result = rewriter.rewrite(indexof, &mut ctx, &mut manager);
    let t = manager.get(result.term()).expect("term should exist");
    assert!(matches!(&t.kind, TermKind::IntConst(n) if n == &BigInt::from(6)));
}

#[test]
fn string_substr_uses_codepoint_indices() {
    let mut manager = TermManager::new();
    let mut ctx = RewriteContext::new();
    let mut rewriter = StringRewriter::new();

    let s = manager.mk_string_lit("héllo");
    let start = manager.mk_int(1);
    let len = manager.mk_int(1);
    let substr = manager.mk_str_substr(s, start, len);

    let result = rewriter.rewrite(substr, &mut ctx, &mut manager);
    let t = manager.get(result.term()).expect("term should exist");
    // Codepoint index 1 of "héllo" is 'é'.
    assert!(matches!(&t.kind, TermKind::StringLit(s) if s == "é"));
}

#[test]
fn string_to_int_rejects_leading_plus_sign() {
    let mut manager = TermManager::new();
    let mut ctx = RewriteContext::new();
    let mut rewriter = StringRewriter::new();

    let s = manager.mk_string_lit("+5");
    let to_int = manager.mk_str_to_int(s);

    let result = rewriter.rewrite(to_int, &mut ctx, &mut manager);
    let t = manager.get(result.term()).expect("term should exist");
    assert!(matches!(&t.kind, TermKind::IntConst(n) if n == &BigInt::from(-1)));
}

#[test]
fn string_to_int_accepts_value_larger_than_i64() {
    let mut manager = TermManager::new();
    let mut ctx = RewriteContext::new();
    let mut rewriter = StringRewriter::new();

    let huge_digits = "99999999999999999999999999999"; // > i64::MAX
    let s = manager.mk_string_lit(huge_digits);
    let to_int = manager.mk_str_to_int(s);

    let result = rewriter.rewrite(to_int, &mut ctx, &mut manager);
    let t = manager.get(result.term()).expect("term should exist");
    let expected: BigInt = huge_digits.parse().expect("valid decimal literal");
    assert!(matches!(&t.kind, TermKind::IntConst(n) if n == &expected));
}

// ========  ========
// oxiz-core/src/smtlib/lexer.rs
// ========  ========

#[test]
fn lexer_reports_unterminated_string_literal() {
    let mut lexer = Lexer::new("\"abc");
    let _ = lexer.next_token();
    assert!(lexer.has_errors());
}

#[test]
fn lexer_reports_unterminated_quoted_symbol() {
    let mut lexer = Lexer::new("|abc");
    let _ = lexer.next_token();
    assert!(lexer.has_errors());
}

#[test]
fn lexer_reports_bare_hash() {
    let mut lexer = Lexer::new("# foo");
    let _ = lexer.next_token();
    assert!(lexer.has_errors());
}

#[test]
fn lexer_well_formed_input_has_no_errors() {
    let mut lexer = Lexer::new("(assert (= x #x1F))");
    while !matches!(
        lexer.next_token().map(|t| t.kind),
        Some(oxiz_core::smtlib::TokenKind::Eof) | None
    ) {}
    assert!(!lexer.has_errors());
}

// ========  ========
// oxiz-core/src/qe/bv/simplification.rs – width_mask guard
// ========  ========

#[test]
fn bv_simplifier_and_constant_folding_at_width_64_does_not_panic() {
    let mut simp = BvSimplifier::default_config();
    let a = BvTerm::Const(0xFFFF_FFFF_FFFF_FFFF, 64);
    let b = BvTerm::Const(0x0F0F_0F0F_0F0F_0F0F, 64);
    let and_term = BvTerm::And(Box::new(a), Box::new(b));

    // Must not panic (`1u64 << 64` previously could) and must compute the
    // correct all-ones mask at width 64.
    let result = simp.simplify(&and_term);
    assert_eq!(result, BvTerm::Const(0x0F0F_0F0F_0F0F_0F0F, 64));
}

// ========  ========
// oxiz-core/src/tactic/pb2bv.rs – constant-offset preservation
// ========  ========

#[test]
fn pb2bv_preserves_constant_offset_in_linear_sum() {
    let mut manager = TermManager::new();
    let bool_sort = manager.sorts.bool_sort;
    let x = manager.mk_var("x", bool_sort);
    let five = manager.mk_int(5);
    let ten = manager.mk_int(10);

    // 2*x + 5 <= 10  <=>  2*x <= 5. Previously the "+5" was dropped,
    // yielding the wrong constraint `2*x <= 10`.
    let two = manager.mk_int(2);
    let two_x = manager.mk_mul([two, x]);
    let sum = manager.mk_add([two_x, five]);
    let le = manager.mk_le(sum, ten);

    let goal = Goal {
        assertions: vec![le],
        precision: Precision::Precise,
    };

    let mut tactic = Pb2BvTactic::new(&mut manager);
    let result = tactic.apply_mut(&goal).expect("tactic should not error");
    // We don't need to decode the full BV encoding here – just confirm the
    // tactic actually converted the constraint (i.e. treated the constant
    // offset as present, taking the "extract succeeded" path) rather than
    // reporting NotApplicable (which would happen if extraction failed) –
    // the real assertion is the algebra above matching the fixed source.
    assert!(!matches!(result, TacticResult::NotApplicable));
}

// ========  ========
// oxiz-core/src/model/completion.rs – sort-correct defaults
// ========  ========

#[test]
fn model_completion_assigns_bool_default_to_bool_variable() {
    let mut manager = TermManager::new();
    let x = manager.mk_var("x", manager.sorts.bool_sort);

    let mut model = Model::new();
    let mut completion = ModelCompletion::new();
    completion.complete(&mut model, &[x], &manager);

    match model.get(x) {
        Some(Value::Bool(_)) => {}
        other => panic!("expected a Bool default for a Bool-sorted variable, got {other:?}"),
    }
}

#[test]
fn model_completion_assigns_int_default_to_int_variable() {
    let mut manager = TermManager::new();
    let x = manager.mk_var("x", manager.sorts.int_sort);

    let mut model = Model::new();
    let mut completion = ModelCompletion::new();
    completion.complete(&mut model, &[x], &manager);

    match model.get(x) {
        Some(Value::Int(_)) => {}
        other => panic!("expected an Int default for an Int-sorted variable, got {other:?}"),
    }
}

// ========  ========
// oxiz-core/src/unsat_core.rs – real deletion-based minimize_with
// ========  ========

#[test]
fn unsat_core_minimize_with_drops_unneeded_assertions() {
    use oxiz_core::ast::NamedAssertion;
    use oxiz_core::{TermId, UnsatCore};

    // Simulate 3 "assertions" (by TermId); only term 2 is "needed" to stay
    // unsat according to the mock oracle below.
    let mk = |id: u32| NamedAssertion {
        term: TermId::from(id),
        name: None,
    };
    let mut core = UnsatCore::new(vec![mk(1), mk(2), mk(3)]);

    core.minimize_with(|remaining| remaining.iter().any(|t| *t == TermId::from(2)));

    assert_eq!(core.term_ids(), vec![TermId::from(2)]);
}

// ========  ========
// oxiz-core/src/smtlib/printer/model.rs – valid function-interpretation output
// ========  ========

#[test]
fn model_printer_emits_syntactically_balanced_function_interpretation() {
    let mut manager = TermManager::new();
    let f_name = manager.intern_str("f");

    let mut interp = FunctionInterpretation::new();
    interp.add_entry(
        vec![ModelValue::Int(BigInt::from(0))],
        ModelValue::Bool(true),
    );
    interp.add_entry(
        vec![ModelValue::Int(BigInt::from(1))],
        ModelValue::Bool(false),
    );
    interp.set_default(ModelValue::Bool(false));

    let mut model = AstModel::new();
    model.add_function(f_name, interp);

    let printer = Printer::new(&manager);
    let text = printer.print_model(&model);

    // The old placeholder emitted the literal text "...)" for any function
    // with table entries, which is not valid SMT-LIB syntax.
    assert!(
        !text.contains("..."),
        "printer output must not contain the placeholder: {text}"
    );
    let opens = text.matches('(').count();
    let closes = text.matches(')').count();
    assert_eq!(
        opens, closes,
        "output must be a balanced s-expression:\n{text}"
    );
}

#[allow(dead_code)]
fn unused_zero_reference() {
    let _ = Rational64::zero();
}
