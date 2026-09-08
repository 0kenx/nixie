use super::*;
use nixie_core::ast::bv_fold;

/// Evaluate the generated BV DAG independently of bit-blasting. Every node is
/// interned after its operands; Boolean values use 0/1 in this test interpreter.
fn circuit_value(c: &Circuit, root: Expr, inputs: &[(Expr, BigInt)]) -> BigUint {
    let m = c.manager.borrow();
    let mut values: Vec<BigInt> = Vec::new();
    for i in 0..m.len() {
        let id = TermId(i as u32);
        let t = m.get(id).expect("arena node");
        if let Some((_, v)) = inputs.iter().find(|(w, _)| w.id == id) {
            values.push(v.clone());
            continue;
        }
        let width = m
            .sorts
            .get(t.sort)
            .and_then(|s| s.bitvec_width())
            .unwrap_or(0);
        let v = |a: TermId| &values[a.0 as usize];
        let b = |a: TermId| !v(a).is_zero();
        let bit = |x: bool| BigInt::from(u8::from(x));
        let value = match &t.kind {
            TermKind::True => BigInt::from(1),
            TermKind::False => BigInt::ZERO,
            TermKind::BitVecConst { value, .. } => value.clone(),
            TermKind::Not(a) => bit(!b(*a)),
            TermKind::And(xs) => bit(xs.iter().all(|&a| b(a))),
            TermKind::Or(xs) => bit(xs.iter().any(|&a| b(a))),
            TermKind::Eq(a, d) => bit(v(*a) == v(*d)),
            TermKind::Ite(a, d, e) => {
                if b(*a) {
                    v(*d).clone()
                } else {
                    v(*e).clone()
                }
            }
            TermKind::BvAdd(a, d) => bv_fold::bv_add(v(*a), v(*d), width),
            TermKind::BvSub(a, d) => bv_fold::bv_sub(v(*a), v(*d), width),
            TermKind::BvMul(a, d) => bv_fold::bv_mul(v(*a), v(*d), width),
            TermKind::BvOr(a, d) => bv_fold::bv_or(v(*a), v(*d), width),
            TermKind::BvXor(a, d) => bv_fold::bv_xor(v(*a), v(*d), width),
            TermKind::BvShl(a, d) => bv_fold::bv_shl(v(*a), v(*d), width),
            TermKind::BvLshr(a, d) => bv_fold::bv_lshr(v(*a), v(*d), width),
            TermKind::BvUlt(a, d) => bit(v(*a) < v(*d)),
            TermKind::BvSlt(a, d) => {
                let aw = m
                    .sorts
                    .get(m.get(*a).expect("lhs").sort)
                    .and_then(|s| s.bitvec_width())
                    .expect("BV width");
                bit(bv_fold::to_signed(v(*a), aw) < bv_fold::to_signed(v(*d), aw))
            }
            TermKind::BvExtract { arg, low, .. } => {
                bv_fold::bv_wrap_unsigned(&(v(*arg) >> *low), width)
            }
            TermKind::BvConcat(a, d) => {
                let dw = m
                    .sorts
                    .get(m.get(*d).expect("rhs").sort)
                    .and_then(|s| s.bitvec_width())
                    .expect("BV width");
                (v(*a) << dw) | v(*d)
            }
            k => panic!("unexpected circuit node {k:?}"),
        };
        values.push(value);
    }
    values[root.id.0 as usize]
        .to_biguint()
        .expect("unsigned output")
}

fn check_circuit(f: FpFormat, pairs: &[(u64, u64)]) {
    let pairs: Vec<_> = pairs
        .iter()
        .map(|&(a, b)| (BigUint::from(a), BigUint::from(b)))
        .collect();
    check_circuit_big(f, &pairs);
}

fn check_circuit_big(f: FpFormat, pairs: &[(BigUint, BigUint)]) {
    for rm in RoundingMode::ALL {
        for op in [Arithmetic::Add, Arithmetic::Sub, Arithmetic::Mul] {
            let c = Circuit::new();
            let x = c.fresh(f.width());
            let y = c.fresh(f.width());
            let result = match op {
                Arithmetic::Add => c.fp_add(x, y, f, rm),
                Arithmetic::Sub => c.fp_add(x, c.fp_neg(y), f, rm),
                Arithmetic::Mul => c.fp_mul(x, y, f, rm),
            };
            for (a, b) in pairs {
                let av = decode(a.clone(), f).expect("a");
                let bv = decode(b.clone(), f).expect("b");
                let expected = arithmetic(op, rm, av, bv).expect("exact oracle");
                let raw = circuit_value(
                    &c,
                    result,
                    &[(x, BigInt::from(a.clone())), (y, BigInt::from(b.clone()))],
                );
                let actual = decode(raw, f).expect("circuit result");
                assert!(
                    Value::Fp(actual).same(Value::Fp(expected)),
                    "{f:?} {op:?} {rm:?} inputs {av:?}, {bv:?}: actual {actual:?}, expected {expected:?}"
                );
            }
        }
    }
}

#[test]
fn maximum_supported_fields_preserve_bits_above_u64() {
    let f = FpFormat::new(15, 64);
    let one = BigUint::from(1u8);
    let sign = &one << 78;
    let frac = (&one << 63) - &one;
    let inf = BigUint::from(32767u32) << 63;
    let max = &inf - &one;
    let normal_one = BigUint::from(16383u32) << 63;
    let points = [BigUint::ZERO, one, frac, normal_one, max, inf];
    let signed: Vec<_> = points
        .into_iter()
        .flat_map(|v| [v.clone(), v | &sign])
        .collect();
    let pairs: Vec<_> = signed
        .iter()
        .flat_map(|a| signed.iter().map(move |b| (a.clone(), b.clone())))
        .collect();
    check_circuit_big(f, &pairs);
}

#[test]
fn exhaustive_tiny_arithmetic_circuits() {
    for f in [
        FpFormat::new(2, 2),
        FpFormat::new(3, 2),
        FpFormat::new(2, 3),
    ] {
        let bound = 1u64 << f.width();
        let pairs: Vec<_> = (0..bound)
            .flat_map(|a| (0..bound).map(move |b| (a, b)))
            .collect();
        check_circuit(f, &pairs);
    }
}

#[test]
fn binary64_rounding_boundaries_and_random_circuits() {
    let boundary = [
        0,
        1,
        2,
        0x000f_ffff_ffff_ffff,
        0x0010_0000_0000_0000,
        0x3ca0_0000_0000_0000,
        0x3ff0_0000_0000_0000,
        0x3ff0_0000_0000_0001,
        0x7fef_ffff_ffff_ffff,
        0x7ff0_0000_0000_0000,
        0x7ff0_0000_0000_0001,
    ];
    let signed: Vec<_> = boundary
        .iter()
        .flat_map(|&x| [x, x | (1u64 << 63)])
        .collect();
    let mut pairs: Vec<_> = signed
        .iter()
        .flat_map(|&a| signed.iter().map(move |&b| (a, b)))
        .collect();
    let mut state = 0x824d_b17a_5912_1234u64;
    for _ in 0..256 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let a = state;
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
        pairs.push((a, state));
    }
    check_circuit(FpFormat::FLOAT64, &pairs);
}

#[test]
fn exponent_and_precision_asymmetry() {
    // Wider intermediate exponents are necessary for (2, 60), even though
    // the format's stored exponent itself needs only two bits.
    for f in [FpFormat::new(2, 60), FpFormat::new(15, 2)] {
        let max = (1u64 << f.width()) - 1;
        check_circuit(
            f,
            &[
                (0, 0),
                (1, 1),
                (max >> 1, 1),
                (max / 3, max / 5),
                (max - 1, max >> 2),
            ],
        );
    }
}

fn goal_from(m: &TermManager, roots: &[TermId]) -> Goal {
    Goal::parse(roots, m).expect("supported goal")
}

#[test]
fn order_cycle_needs_no_sat_search() {
    let mut m = TermManager::new();
    let sort = m.sorts.float64_sort();
    let a = m.mk_var("a", sort);
    let b = m.mk_var("b", sort);
    let d = m.mk_var("d", sort);
    let roots = [m.mk_fp_lt(a, b), m.mk_fp_leq(b, d), m.mk_fp_leq(d, a)];
    let (result, _, stats) = solve(&goal_from(&m, &roots), 0).expect("solve");
    assert_eq!(result, SolverResult::Unsat);
    assert_eq!(stats.checks, 0);
}

#[test]
fn datum_congruence_refutes_arithmetic_without_refinement() {
    let mut m = TermManager::new();
    let sort = m.sorts.float64_sort();
    let a = m.mk_var("a", sort);
    let b = m.mk_var("b", sort);
    let aa = m.mk_fp_mul(RoundingMode::RNA, a, a);
    let bb = m.mk_fp_mul(RoundingMode::RNA, b, b);
    let equal = m.mk_eq(a, b);
    let same = m.mk_eq(aa, bb);
    let different = m.mk_not(same);
    let (result, _, stats) = solve(&goal_from(&m, &[equal, different]), 0).expect("solve");
    assert_eq!(result, SolverResult::Unsat);
    assert_eq!(stats.checks, 0);
}

#[test]
fn ieee_equality_does_not_imply_sign_congruence() {
    let mut m = TermManager::new();
    let sort = m.sorts.float_sort(3, 4);
    let a = m.mk_var("a", sort);
    let b = m.mk_var("b", sort);
    let roots = [
        m.mk_fp_eq(a, b),
        m.mk_fp_is_positive(a),
        m.mk_fp_is_negative(b),
    ];
    assert_eq!(
        solve(&goal_from(&m, &roots), 0).expect("solve").0,
        SolverResult::Sat
    );
}

#[test]
fn backward_classes_refute_zero_times_finite_without_blasting() {
    let mut m = TermManager::new();
    let sort = m.sorts.float64_sort();
    let a = m.mk_var("a", sort);
    let b = m.mk_var("b", sort);
    let p = m.mk_fp_mul(RoundingMode::RNE, a, b);
    let roots = [
        m.mk_fp_is_zero(a),
        m.mk_fp_is_normal(b),
        m.mk_fp_is_normal(p),
    ];
    let (result, _, stats) = solve(&goal_from(&m, &roots), 0).expect("solve");
    assert_eq!(result, SolverResult::Unsat);
    assert_eq!(stats.exact_operations, 0);
}

#[test]
fn symbolic_arithmetic_refines_and_returns_verified_model() {
    let mut m = TermManager::new();
    let sort = m.sorts.float_sort(3, 4);
    let a = m.mk_var("a", sort);
    let sum = m.mk_fp_add(RoundingMode::RNE, a, a);
    let three = m.mk_fp_lit(false, BigInt::from(4), BigInt::from(4), 3, 4);
    let roots = [m.mk_eq(sum, three)];
    let (result, values, stats) = solve(&goal_from(&m, &roots), 0).expect("solve");
    assert_eq!(result, SolverResult::Sat);
    assert!(!values.is_empty());
    assert_eq!(stats.exact_operations, 1);
}

#[test]
fn candidate_refinement_cannot_accept_a_negative_square() {
    let mut m = TermManager::new();
    let sort = m.sorts.float_sort(3, 4);
    let a = m.mk_var("a", sort);
    let square = m.mk_fp_mul(RoundingMode::RNE, a, a);
    let minus_one = m.mk_fp_lit(true, BigInt::from(3), BigInt::ZERO, 3, 4);
    let roots = [m.mk_eq(square, minus_one)];
    let (result, _, _) = solve(&goal_from(&m, &roots), 0).expect("solve");
    assert_eq!(result, SolverResult::Unsat);
}

#[test]
fn inactive_boolean_branch_does_not_assert_fp_facts() {
    let mut m = TermManager::new();
    let sort = m.sorts.float64_sort();
    let a = m.mk_var("a", sort);
    let nan = m.mk_fp_is_nan(a);
    let normal = m.mk_fp_is_normal(a);
    let or = m.mk_or(vec![nan, normal]);
    let roots = [or, nan];
    assert_eq!(
        solve(&goal_from(&m, &roots), 0).expect("solve").0,
        SolverResult::Sat
    );
}

#[test]
fn unsupported_operators_and_malformed_sorts_are_declined() {
    let mut m = TermManager::new();
    let sort = m.sorts.float64_sort();
    let a = m.mk_var("a", sort);
    let div = m.mk_fp_div(RoundingMode::RNE, a, a);
    let pred = m.mk_fp_is_normal(div);
    assert!(Goal::parse(&[pred], &m).is_none());
    let wrong = m.intern_term(TermKind::FpAdd(RoundingMode::RNE, a, m.true_id), sort);
    let pred = m.mk_fp_is_normal(wrong);
    assert!(Goal::parse(&[pred], &m).is_none());
    let wide = m.sorts.float128_sort();
    let w = m.mk_var("wide", wide);
    let pred = m.mk_fp_is_normal(w);
    assert!(Goal::parse(&[pred], &m).is_none());
}

#[test]
fn deep_boolean_dag_is_collected_and_encoded_without_recursion() {
    let mut m = TermManager::new();
    let sort = m.sorts.float_sort(3, 4);
    let x = m.mk_var("x", sort);
    let mut root = m.mk_fp_is_normal(x);
    for _ in 0..12_000 {
        root = m.intern_term(TermKind::Not(root), m.sorts.bool_sort);
    }
    assert_eq!(
        solve(&goal_from(&m, &[root]), 0).expect("solve deep DAG").0,
        SolverResult::Sat
    );
}

#[test]
fn hybrid_scope_and_public_model_roundtrip() {
    let mut ctx = crate::Context::new();
    let output = ctx
        .execute_script(
            "(set-logic QF_FP)
        (set-option :produce-models true)
        (declare-const x (_ FloatingPoint 3 4))
        (assert (= (fp.add RNE x x) (fp #b0 #b100 #b100)))
        (check-sat) (get-value (x))
        (push 1) (assert (fp.isNegative x)) (check-sat)
        (pop 1) (check-sat) (get-value (x))",
        )
        .expect("parse script");
    let verdicts: Vec<_> = output
        .iter()
        .filter(|x| ["sat", "unsat", "unknown"].contains(&x.trim()))
        .map(|x| x.trim())
        .collect();
    assert_eq!(verdicts, vec!["sat", "unsat", "sat"], "{output:?}");
    assert!(
        output.iter().filter(|s| s.contains("#b")).count() >= 2,
        "concrete get-value: {output:?}"
    );
}
