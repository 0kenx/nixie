//! Regression tests for the P1 parser wave (SMT-LIB `FloatingPoint` /
//! `FixedSizeBitVectors` extensions, sort/lexer robustness).
//!
//! Each test reproduces one specific defect fixed in this wave and asserts
//! the corrected behavior:
//!
//! - FP-TOFP-01: indexed `to_fp`/`to_fp_unsigned`/`fp.to_sbv`/`fp.to_ubv`
//!   must accept their leading rounding-mode argument.
//! - BV-NEG-01: `bvneg` must be recognized (was a Bool-sorted uninterpreted
//!   apply).
//! - BV-EXT-01: `bvnand`/`bvnor`/`bvxnor`/`bvcomp`/`bvsmod` must be
//!   recognized and correctly typed.
//! - FP-CONV-SIB-01: `fp.to_real`, the `(fp sign exp sig)` literal, and the
//!   indexed FP special-value constants must be recognized.
//! - SORT-BUILTIN-01: `RoundingMode`/`RegLan` must not silently become
//!   ordinary uninterpreted sorts.
//! - R1: `parse_sort` must not overflow the stack on deeply nested sorts.
//! - todo-1151: `mk_bv_concat` must not silently fabricate a width for a
//!   non-bit-vector operand.
//! - todo-1174: the lexer must reject leading-zero numerals and must not
//!   truncate `(_ bvN M)` literal values to `i64`.

use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::smtlib::{Command, Lexer, Printer, parse_script};
use oxiz_core::sort::SortKind;

/// Parse a full script, returning the manager plus the asserted term ids in
/// order.
fn parse_asserts(script: &str) -> (TermManager, Vec<TermId>) {
    let mut manager = TermManager::new();
    let commands = parse_script(script, &mut manager).expect("script should parse");
    let asserts = commands
        .into_iter()
        .filter_map(|c| match c {
            Command::Assert(t) => Some(t),
            _ => None,
        })
        .collect();
    (manager, asserts)
}

fn kind(manager: &TermManager, t: TermId) -> TermKind {
    manager.get(t).expect("term should exist").kind.clone()
}

fn sort_kind(manager: &TermManager, t: TermId) -> SortKind {
    let sort = manager.get(t).expect("term should exist").sort;
    manager
        .sorts
        .get(sort)
        .expect("sort should exist")
        .kind
        .clone()
}

/// Return the two operand term ids of an equality (`mk_eq` canonicalizes
/// operand order by raw `TermId`, so callers must not assume which side is
/// which — this is the same helper pattern used by `audit_parser_terms.rs`).
fn eq_operands(m: &TermManager, t: TermId) -> (TermId, TermId) {
    match kind(m, t) {
        TermKind::Eq(a, b) => (a, b),
        other => panic!("expected equality, got {other:?}"),
    }
}

/// Find, among the two operands of an equality, the one satisfying `pred`.
fn eq_side_matching(m: &TermManager, t: TermId, pred: impl Fn(&TermKind) -> bool) -> TermId {
    let (a, b) = eq_operands(m, t);
    if pred(&kind(m, a)) {
        a
    } else if pred(&kind(m, b)) {
        b
    } else {
        panic!(
            "neither operand matched: {:?} / {:?}",
            kind(m, a),
            kind(m, b)
        )
    }
}

/// Re-print a term via the basic printer and confirm the printed form
/// re-parses, *under a real strict script* that first re-declares every free
/// variable `t` depends on with its original sort (`decls`), to a term of
/// the same sort as `t`. This deliberately avoids `parse_term`'s lenient
/// bare-term mode, which defaults any undeclared symbol to `Bool` and would
/// silently "round-trip" even a wrongly-typed printed form.
fn assert_round_trips(manager: &TermManager, t: TermId, decls: &[&str]) {
    let printer = Printer::new(manager);
    let printed = printer.print_term(t);
    let sort_id = manager.get(t).expect("term should exist").sort;
    let mut sort_str = String::new();
    printer.write_sort(&mut sort_str, sort_id);

    let mut script = String::new();
    for d in decls {
        script.push_str(d);
        script.push('\n');
    }
    script.push_str(&format!("(declare-const __round_trip__ {sort_str})\n"));
    script.push_str(&format!("(assert (= __round_trip__ {printed}))\n"));

    let mut fresh = TermManager::new();
    parse_script(&script, &mut fresh)
        .unwrap_or_else(|e| panic!("round-trip script failed to parse:\n{script}\nerror: {e:?}"));
}

// ---------------------------------------------------------------------------
// FP-TOFP-01: indexed to_fp / to_fp_unsigned / fp.to_sbv / fp.to_ubv must
// accept a rounding-mode first argument.
// ---------------------------------------------------------------------------

#[test]
fn to_fp_from_real_accepts_rounding_mode() {
    let (m, asserts) = parse_asserts(
        r#"
        (set-logic QF_FP)
        (declare-const a (_ FloatingPoint 11 53))
        (assert (= a ((_ to_fp 11 53) RNE 10.0)))
        "#,
    );
    let rhs = eq_side_matching(&m, asserts[0], |k| matches!(k, TermKind::RealToFp { .. }));
    match kind(&m, rhs) {
        TermKind::RealToFp { eb, sb, .. } => assert_eq!((eb, sb), (11, 53)),
        other => panic!("expected RealToFp, got {other:?}"),
    }
    // Not round-tripped: the pre-existing basic printer formats whole-number
    // `Real` constants (e.g. the `10.0` above) without a decimal point
    // (`{r}` on the underlying `Rational64`, e.g. "10"), which then re-lexes
    // as an `Int` numeral rather than a `Real` decimal — a separate,
    // out-of-scope printer defect (any `Real`-typed round trip through this
    // printer hits it, not just this operator).
}

#[test]
fn to_fp_from_bitvec_dispatches_to_signed_conversion() {
    let (m, asserts) = parse_asserts(
        r#"
        (set-logic QF_FP)
        (declare-const bv (_ BitVec 32))
        (declare-const a (_ FloatingPoint 8 24))
        (assert (= a ((_ to_fp 8 24) RTZ bv)))
        "#,
    );
    let rhs = eq_side_matching(&m, asserts[0], |k| matches!(k, TermKind::SBVToFp { .. }));
    match kind(&m, rhs) {
        TermKind::SBVToFp { eb, sb, .. } => assert_eq!((eb, sb), (8, 24)),
        other => panic!("expected SBVToFp, got {other:?}"),
    }
    assert_round_trips(&m, rhs, &["(declare-const bv (_ BitVec 32))"]);
}

#[test]
fn to_fp_unsigned_accepts_rounding_mode() {
    let (m, asserts) = parse_asserts(
        r#"
        (set-logic QF_FP)
        (declare-const bv (_ BitVec 16))
        (declare-const a (_ FloatingPoint 5 11))
        (assert (= a ((_ to_fp_unsigned 5 11) RTP bv)))
        "#,
    );
    let rhs = eq_side_matching(&m, asserts[0], |k| matches!(k, TermKind::UBVToFp { .. }));
    match kind(&m, rhs) {
        TermKind::UBVToFp { eb, sb, .. } => assert_eq!((eb, sb), (5, 11)),
        other => panic!("expected UBVToFp, got {other:?}"),
    }
    assert_round_trips(&m, rhs, &["(declare-const bv (_ BitVec 16))"]);
}

#[test]
fn fp_to_sbv_and_to_ubv_accept_rounding_mode() {
    let (m, asserts) = parse_asserts(
        r#"
        (set-logic QF_FP)
        (declare-const a (_ FloatingPoint 8 24))
        (declare-const b (_ FloatingPoint 8 24))
        (assert (= ((_ fp.to_sbv 32) RTZ a) ((_ fp.to_ubv 32) RTZ b)))
        "#,
    );
    let (lhs, rhs) = eq_operands(&m, asserts[0]);
    let sbv_side = if matches!(kind(&m, lhs), TermKind::FpToSBV { .. }) {
        lhs
    } else {
        rhs
    };
    let ubv_side = if sbv_side == lhs { rhs } else { lhs };
    match kind(&m, sbv_side) {
        TermKind::FpToSBV { width, .. } => assert_eq!(width, 32),
        other => panic!("expected FpToSBV, got {other:?}"),
    }
    match kind(&m, ubv_side) {
        TermKind::FpToUBV { width, .. } => assert_eq!(width, 32),
        other => panic!("expected FpToUBV, got {other:?}"),
    }
    let decls: &[&str] = &[
        "(declare-const a (_ FloatingPoint 8 24))",
        "(declare-const b (_ FloatingPoint 8 24))",
    ];
    assert_round_trips(&m, sbv_side, decls);
    assert_round_trips(&m, ubv_side, decls);
}

// ---------------------------------------------------------------------------
// BV-NEG-01: bvneg must be recognized.
// ---------------------------------------------------------------------------

#[test]
fn bvneg_is_recognized() {
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const x (_ BitVec 8))
        (assert (= (bvneg x) #x00))
        "#,
    );
    // mk_bv_neg lowers to two's-complement negation `0 - x`; pre-fix this
    // was an unrecognized Bool-sorted uninterpreted apply of "bvneg".
    let neg_side = eq_side_matching(&m, asserts[0], |k| matches!(k, TermKind::BvSub(..)));
    match kind(&m, neg_side) {
        TermKind::BvSub(zero, arg) => {
            assert!(matches!(
                kind(&m, zero),
                TermKind::BitVecConst { width: 8, .. }
            ));
            assert_eq!(sort_kind(&m, arg), SortKind::BitVec(8));
        }
        other => panic!("expected bvneg to lower to BvSub, got {other:?}"),
    }
    assert_eq!(sort_kind(&m, neg_side), SortKind::BitVec(8));
    assert_round_trips(&m, neg_side, &["(declare-const x (_ BitVec 8))"]);
}

// ---------------------------------------------------------------------------
// BV-EXT-01: bvnand, bvnor, bvxnor, bvcomp, bvsmod must be recognized.
// ---------------------------------------------------------------------------

#[test]
fn bvnand_lowers_to_not_and() {
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const a (_ BitVec 4))
        (declare-const b (_ BitVec 4))
        (declare-const c (_ BitVec 4))
        (assert (= (bvnand a b) c))
        "#,
    );
    let nand_side = eq_side_matching(&m, asserts[0], |k| matches!(k, TermKind::BvNot(..)));
    match kind(&m, nand_side) {
        TermKind::BvNot(inner) => assert!(matches!(kind(&m, inner), TermKind::BvAnd(..))),
        other => panic!("expected bvnand to lower to BvNot(BvAnd(..)), got {other:?}"),
    }
    assert_eq!(sort_kind(&m, nand_side), SortKind::BitVec(4));
    let decls: &[&str] = &[
        "(declare-const a (_ BitVec 4))",
        "(declare-const b (_ BitVec 4))",
    ];
    assert_round_trips(&m, nand_side, decls);
}

#[test]
fn bvnor_lowers_to_not_or() {
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const a (_ BitVec 4))
        (declare-const b (_ BitVec 4))
        (declare-const c (_ BitVec 4))
        (assert (= (bvnor a b) c))
        "#,
    );
    let nor_side = eq_side_matching(&m, asserts[0], |k| matches!(k, TermKind::BvNot(..)));
    match kind(&m, nor_side) {
        TermKind::BvNot(inner) => assert!(matches!(kind(&m, inner), TermKind::BvOr(..))),
        other => panic!("expected bvnor to lower to BvNot(BvOr(..)), got {other:?}"),
    }
    let decls: &[&str] = &[
        "(declare-const a (_ BitVec 4))",
        "(declare-const b (_ BitVec 4))",
    ];
    assert_round_trips(&m, nor_side, decls);
}

#[test]
fn bvxnor_lowers_to_not_xor() {
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const a (_ BitVec 4))
        (declare-const b (_ BitVec 4))
        (declare-const c (_ BitVec 4))
        (assert (= (bvxnor a b) c))
        "#,
    );
    let xnor_side = eq_side_matching(&m, asserts[0], |k| matches!(k, TermKind::BvNot(..)));
    match kind(&m, xnor_side) {
        TermKind::BvNot(inner) => assert!(matches!(kind(&m, inner), TermKind::BvXor(..))),
        other => panic!("expected bvxnor to lower to BvNot(BvXor(..)), got {other:?}"),
    }
    let decls: &[&str] = &[
        "(declare-const a (_ BitVec 4))",
        "(declare-const b (_ BitVec 4))",
    ];
    assert_round_trips(&m, xnor_side, decls);
}

#[test]
fn bvcomp_produces_a_single_bit_result() {
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const a (_ BitVec 4))
        (declare-const b (_ BitVec 4))
        (declare-const c (_ BitVec 1))
        (assert (= (bvcomp a b) c))
        "#,
    );
    let comp_side = eq_side_matching(&m, asserts[0], |k| matches!(k, TermKind::Ite(..)));
    assert_eq!(sort_kind(&m, comp_side), SortKind::BitVec(1));
    let decls: &[&str] = &[
        "(declare-const a (_ BitVec 4))",
        "(declare-const b (_ BitVec 4))",
    ];
    assert_round_trips(&m, comp_side, decls);
}

#[test]
fn bvsmod_is_recognized_and_correctly_typed() {
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const a (_ BitVec 8))
        (declare-const b (_ BitVec 8))
        (declare-const c (_ BitVec 8))
        (assert (= (bvsmod a b) c))
        "#,
    );
    // Pre-fix this degraded to a Bool-sorted `Apply("bvsmod", ..)`; it must
    // now build a genuine bit-vector-sorted term (the SMT-LIB `bvsmod`
    // definition's outermost connective is an `ite`).
    let smod_side = eq_side_matching(&m, asserts[0], |k| matches!(k, TermKind::Ite(..)));
    assert_eq!(sort_kind(&m, smod_side), SortKind::BitVec(8));
    let decls: &[&str] = &[
        "(declare-const a (_ BitVec 8))",
        "(declare-const b (_ BitVec 8))",
    ];
    assert_round_trips(&m, smod_side, decls);
}

// ---------------------------------------------------------------------------
// FP-CONV-SIB-01: fp.to_real, the (fp ...) literal, and indexed FP special
// values must be recognized.
// ---------------------------------------------------------------------------

#[test]
fn fp_to_real_is_recognized() {
    let (m, asserts) = parse_asserts(
        r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const r Real)
        (assert (= r (fp.to_real x)))
        "#,
    );
    let rhs = eq_side_matching(&m, asserts[0], |k| matches!(k, TermKind::FpToReal(_)));
    assert_eq!(sort_kind(&m, rhs), SortKind::Real);
    assert_round_trips(&m, rhs, &["(declare-const x (_ FloatingPoint 8 24))"]);
}

#[test]
fn fp_literal_bit_triple_constructor_is_recognized() {
    // float32: eb=8, sb=24 -> sign is 1 bit, exponent is 8 bits, the
    // significand literal here is the 23 explicit (non-hidden) bits.
    let (m, asserts) = parse_asserts(
        r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (= x (fp #b1 #b10000001 #b01000000000000000000000)))
        "#,
    );
    let rhs = eq_side_matching(&m, asserts[0], |k| matches!(k, TermKind::FpLit { .. }));
    match kind(&m, rhs) {
        TermKind::FpLit {
            sign,
            exp,
            sig,
            eb,
            sb,
        } => {
            assert!(sign);
            assert_eq!(exp, num_bigint::BigInt::from(0b10000001));
            assert_eq!(sig, num_bigint::BigInt::from(0b01000000000000000000000i64));
            assert_eq!((eb, sb), (8, 24));
        }
        other => panic!("expected FpLit, got {other:?}"),
    }
    assert_eq!(
        sort_kind(&m, rhs),
        SortKind::FloatingPoint { eb: 8, sb: 24 }
    );
    // Not round-tripped: the pre-existing basic printer formats the FpLit's
    // exponent/significand fields with `#b{decimal_value}` instead of an
    // actual zero-padded binary string (a separate, out-of-scope printer
    // defect), so its printed form is not guaranteed to re-lex as a valid
    // `#b`-literal. Structural verification above is the meaningful check
    // for this parser-level fix.
}

#[test]
fn fp_special_value_constants_are_recognized() {
    let (m, asserts) = parse_asserts(
        r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (fp.eq x (_ +oo 8 24)))
        (assert (fp.eq x (_ -oo 8 24)))
        (assert (fp.eq x (_ +zero 8 24)))
        (assert (fp.eq x (_ -zero 8 24)))
        (assert (fp.eq x (_ NaN 8 24)))
        "#,
    );
    let rhs_of = |t: TermId| match kind(&m, t) {
        TermKind::FpEq(_, b) => b,
        other => panic!("expected FpEq, got {other:?}"),
    };
    assert!(matches!(
        kind(&m, rhs_of(asserts[0])),
        TermKind::FpPlusInfinity { eb: 8, sb: 24 }
    ));
    assert!(matches!(
        kind(&m, rhs_of(asserts[1])),
        TermKind::FpMinusInfinity { eb: 8, sb: 24 }
    ));
    assert!(matches!(
        kind(&m, rhs_of(asserts[2])),
        TermKind::FpPlusZero { eb: 8, sb: 24 }
    ));
    assert!(matches!(
        kind(&m, rhs_of(asserts[3])),
        TermKind::FpMinusZero { eb: 8, sb: 24 }
    ));
    assert!(matches!(
        kind(&m, rhs_of(asserts[4])),
        TermKind::FpNaN { eb: 8, sb: 24 }
    ));
    for &a in &asserts {
        assert_round_trips(&m, rhs_of(a), &[]);
    }
}

// ---------------------------------------------------------------------------
// SORT-BUILTIN-01: RoundingMode / RegLan must not silently become ordinary
// uninterpreted sorts.
// ---------------------------------------------------------------------------

#[test]
fn rounding_mode_sort_is_honestly_rejected_not_silently_uninterpreted() {
    let mut manager = TermManager::new();
    let err = parse_script("(declare-const m RoundingMode)", &mut manager)
        .expect_err("declaring a RoundingMode-sorted constant must not silently succeed");
    let msg = format!("{err:?}").to_lowercase();
    assert!(
        msg.contains("roundingmode"),
        "error should mention RoundingMode: {msg}"
    );
}

#[test]
fn reglan_sort_is_honestly_rejected_not_silently_uninterpreted() {
    let mut manager = TermManager::new();
    let err = parse_script("(declare-const r RegLan)", &mut manager)
        .expect_err("declaring a RegLan-sorted constant must not silently succeed");
    let msg = format!("{err:?}").to_lowercase();
    assert!(msg.contains("reglan"), "error should mention RegLan: {msg}");
}

// ---------------------------------------------------------------------------
// R1: parse_sort must not overflow the stack on deeply nested sorts.
// ---------------------------------------------------------------------------

#[test]
fn deeply_nested_array_sort_is_rejected_not_a_stack_overflow() {
    // Nest well past the 512-level guard via the Array sort's *range*
    // position (right-recursion), matching how `(Array (Array (Array ...
    // Int) Int) Int)` grows in practice.
    let depth = 2000;
    let mut sort_expr = "Int".to_string();
    for _ in 0..depth {
        sort_expr = format!("(Array Int {sort_expr})");
    }
    let script = format!("(declare-const x {sort_expr})");
    let mut manager = TermManager::new();
    let err = parse_script(&script, &mut manager)
        .expect_err("pathologically deep nested sort must be rejected, not overflow the stack");
    let msg = format!("{err:?}").to_lowercase();
    assert!(
        msg.contains("deep") || msg.contains("depth"),
        "error should mention nesting depth: {msg}"
    );
}

#[test]
fn moderately_nested_array_sort_still_parses() {
    // A sanity control: nesting well under the 512-level cap must still
    // parse successfully (the guard must not be so tight it rejects
    // legitimate, if unusual, inputs).
    let depth = 20;
    let mut sort_expr = "Int".to_string();
    for _ in 0..depth {
        sort_expr = format!("(Array Int {sort_expr})");
    }
    let script = format!("(declare-const x {sort_expr})");
    let mut manager = TermManager::new();
    parse_script(&script, &mut manager).expect("moderately nested sort should parse");
}

// ---------------------------------------------------------------------------
// todo-1151: mk_bv_concat must not silently fabricate a width for a
// non-bit-vector operand.
// ---------------------------------------------------------------------------

#[test]
fn bv_concat_computes_exact_combined_width_for_valid_operands() {
    let mut m = TermManager::new();
    let a = m.mk_bitvec(0i64, 5);
    let b = m.mk_bitvec(0i64, 3);
    let concat = m.mk_bv_concat(a, b);
    assert_eq!(sort_kind(&m, concat), SortKind::BitVec(8));
}

// `mk_bv_concat` guards this with `debug_assert!`, which is compiled out in
// release builds (where the documented `32`-width fallback takes over
// instead). The test therefore only exists when debug assertions are on —
// gating it here rather than weakening the assertion keeps the debug-profile
// check exactly as strict as it was.
#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "mk_bv_concat")]
fn bv_concat_debug_asserts_on_non_bitvector_operand() {
    let mut m = TermManager::new();
    let int_term = m.mk_int(5);
    let bv_term = m.mk_bitvec(3i64, 8);
    // A non-bitvector operand must be caught loudly in debug builds rather
    // than silently combined into a fabricated `32 + 8 = 40`-bit result.
    let _ = m.mk_bv_concat(int_term, bv_term);
}

// ---------------------------------------------------------------------------
// todo-1174: lexer leading-zero numerals and arbitrary-precision (_ bvN M).
// ---------------------------------------------------------------------------

#[test]
fn lexer_rejects_leading_zero_numeral() {
    let mut lexer = Lexer::new("007");
    let _ = lexer.next_token();
    assert!(
        lexer.has_errors(),
        "a leading-zero numeral must be recorded as a lexical error"
    );
}

#[test]
fn lexer_accepts_bare_zero_numeral() {
    let mut lexer = Lexer::new("0");
    let _ = lexer.next_token();
    assert!(!lexer.has_errors(), "a bare '0' is a valid SMT-LIB numeral");
}

#[test]
fn lexer_does_not_flag_leading_zeros_in_a_decimals_fractional_part() {
    // The SMT-LIB `<decimal>` grammar is `<numeral>.0*<numeral>`, so a
    // fractional part like the "001" in "0.001" legitimately starts with
    // zeros and must not be flagged.
    let mut lexer = Lexer::new("0.001");
    let _ = lexer.next_token();
    assert!(
        !lexer.has_errors(),
        "leading zeros in a decimal's fractional part are valid"
    );
}

#[test]
fn indexed_bitvector_literal_supports_values_beyond_i64() {
    // i64::MAX = 9223372036854775807 (19 digits); use a value with more
    // digits than that to confirm the parser no longer truncates to i64.
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const x (_ BitVec 128))
        (assert (= x (_ bv123456789012345678901234567890 128)))
        "#,
    );
    let rhs = eq_side_matching(&m, asserts[0], |k| {
        matches!(k, TermKind::BitVecConst { .. })
    });
    match kind(&m, rhs) {
        TermKind::BitVecConst { value, width } => {
            assert_eq!(width, 128);
            let expected: num_bigint::BigInt = "123456789012345678901234567890"
                .parse()
                .expect("literal should parse as BigInt");
            assert_eq!(value, expected);
        }
        other => panic!("expected BitVecConst, got {other:?}"),
    }
}
