//! Independent regressions for the twelve 2026-09-22 theory-audit findings.
#![allow(clippy::unwrap_used)]
use nixie_core::ast::TermId;
use nixie_theories::Theory;
use nixie_theories::array::ArraySolver;
use nixie_theories::combination::{CombinationMode, TheoryCombiner};
use nixie_theories::fp::{FpFormat, FpRoundingMode, FpSolver, FpValue};
use nixie_theories::set::{CardConstraintKind, SetConstraint, SetExpr, SetSolver, SetSort};
use nixie_theories::utvpi::{
    DoubledGraph, DoubledNode, Sign, UtConstraint, UtvpiConfig, UtvpiResult, UtvpiSolver,
};
use nixie_theories::{EqualityNotification, TheoryCheckResult as TheoryResult, TheoryCombination};
use num_rational::{BigRational, Rational64};
fn t(n: u32) -> TermId {
    TermId::new(n)
}
fn r(n: i64) -> Rational64 {
    Rational64::from_integer(n)
}
fn ut(integer: bool, spfa: bool) -> UtvpiSolver {
    UtvpiSolver::with_config(
        integer,
        UtvpiConfig {
            use_spfa: spfa,
            ..Default::default()
        },
    )
}

#[test]
fn f1_candidate_conflicts_are_scoped_and_not_global_refutations() {
    for mode in [CombinationMode::Polite, CombinationMode::ModelBased] {
        let mut c = TheoryCombiner::with_mode(mode);
        // Term IDs deliberately differ from EUF node IDs.
        for term in [t(100), t(200)] {
            c.add_shared_var(term);
            c.arith_mut().intern(term);
        }
        let a = c.euf_mut().intern(t(100));
        let b = c.euf_mut().intern(t(200));
        c.euf_mut().assert_diseq(a, b, t(300));
        assert!(matches!(c.check(), Ok(TheoryResult::Unknown)));
        assert!(!c.euf().are_equal_immutable(a, b));
        assert!(c.get_model().is_empty());
        // The rejected x=y candidate must not poison a later valid model.
        c.arith_mut().assert_eq(&[(t(100), r(1))], r(0), t(301));
        c.arith_mut().assert_eq(&[(t(200), r(1))], r(1), t(302));
        assert!(matches!(c.check(), Ok(TheoryResult::Sat)));
        assert!(!c.euf().are_equal_immutable(a, b));
    }
}

#[test]
fn f2_check_both_sides_of_the_shared_arrangement() {
    for mode in [CombinationMode::Polite, CombinationMode::ModelBased] {
        let mut c = TheoryCombiner::with_mode(mode);
        for v in [t(7), t(9)] {
            c.add_shared_var(v);
            c.arith_mut()
                .assert_eq(&[(v, r(1))], r(0), t(100 + v.raw()));
        }
        let a = c.euf_mut().intern(t(7));
        let b = c.euf_mut().intern(t(9));
        c.euf_mut().assert_diseq(a, b, t(10));
        assert!(matches!(
            c.check(),
            Ok(TheoryResult::Unknown | TheoryResult::Unsat(_))
        ));
        assert!(c.get_model().is_empty());
    }
}

#[test]
fn f3_ground_widening_is_exact() {
    let mut s = FpSolver::new();
    s.assert_const(t(1), &FpValue::from_f32(1.0));
    s.assert_fp_to_fp(t(2), t(1), FpFormat::FLOAT64);
    s.assert_const(t(2), &FpValue::from_f64(2.0));
    assert!(matches!(s.check(), Ok(TheoryResult::Unsat(_))));
    assert!(s.get_value(t(1)).is_none());
}

#[test]
fn f3_symbolic_conversion_declines_without_fabricating_a_model() {
    let mut s = FpSolver::new();
    s.new_fp(t(1), FpFormat::FLOAT32);
    s.assert_fp_to_fp(t(2), t(1), FpFormat::FLOAT64);
    // Constants supplied AFTER the symbolic conversion do not turn the
    // incomplete encoding into a supported one.
    s.assert_const(t(1), &FpValue::from_f32(1.0));
    s.assert_const(t(2), &FpValue::from_f64(2.0));
    assert!(matches!(s.check(), Ok(TheoryResult::Unknown)));
    assert!(s.get_value(t(2)).is_none());
    assert!(s.get_model().is_empty());

    // The ground engine's format guard precedes classification: its narrow
    // exponent helpers cannot classify arbitrary SMT floating-point formats.
    let mut wide = FpSolver::new();
    wide.assert_const(
        t(1),
        &FpValue::pos_zero(FpFormat {
            exponent_bits: 32,
            significand_bits: 2,
        }),
    );
    wide.assert_fp_to_fp(t(2), t(1), FpFormat::FLOAT32);
    assert!(matches!(wide.check(), Ok(TheoryResult::Unknown)));
}

#[test]
fn f3_ground_narrowing_honors_every_rounding_mode() {
    for (mode, up) in [
        (FpRoundingMode::RoundNearestTiesToEven, false),
        (FpRoundingMode::RoundNearestTiesToAway, true),
        (FpRoundingMode::RoundTowardPositive, true),
        (FpRoundingMode::RoundTowardNegative, false),
        (FpRoundingMode::RoundTowardZero, false),
    ] {
        let mut s = FpSolver::new();
        s.set_rounding_mode(mode);
        s.assert_const(t(1), &FpValue::from_f64(1.0 + 2.0f64.powi(-24)));
        s.assert_fp_to_fp(t(2), t(1), FpFormat::FLOAT32);
        assert!(matches!(s.check(), Ok(TheoryResult::Sat)));
        let expected = if up {
            f32::from_bits(1.0f32.to_bits() + 1)
        } else {
            1.0
        };
        assert_eq!(s.get_value(t(2)).and_then(|v| v.to_f32()), Some(expected));
    }
}

#[test]
fn f3_constant_and_model_caches_follow_scopes() {
    let mut s = FpSolver::new();
    s.new_fp(t(1), FpFormat::FLOAT32);
    s.push();
    s.assert_const(t(1), &FpValue::from_f32(1.0));
    assert!(matches!(s.check(), Ok(TheoryResult::Sat)));
    s.pop();
    assert!(s.get_value(t(1)).is_none());
    s.assert_const(t(1), &FpValue::from_f32(2.0));
    s.assert_fp_to_fp(t(2), t(1), FpFormat::FLOAT64);
    assert!(matches!(s.check(), Ok(TheoryResult::Sat)));
    assert_eq!(s.get_value(t(2)).and_then(|v| v.to_f64()), Some(2.0));
    s.push();
    s.assert_fp_to_fp(t(4), t(99), FpFormat::FLOAT64);
    assert!(matches!(s.check(), Ok(TheoryResult::Unknown)));
    s.pop();
    assert!(matches!(s.check(), Ok(TheoryResult::Sat)));
}

fn member(v: nixie_theories::set::SetVarId, e: u32, sign: bool) -> SetConstraint {
    SetConstraint::Member {
        set: SetExpr::Var(v),
        element: e,
        sign,
    }
}
fn card(v: nixie_theories::set::SetVarId, n: i64) -> SetConstraint {
    SetConstraint::Cardinality {
        set: SetExpr::Var(v),
        op: CardConstraintKind::Equal,
        bound: n,
    }
}

#[test]
fn f4_disjointness_survives_later_membership() {
    let mut s = SetSolver::new();
    let a = s.new_set_var("a", SetSort::IntSet);
    let b = s.new_set_var("b", SetSort::IntSet);
    s.add_constraint(SetConstraint::Disjoint {
        lhs: SetExpr::Var(a),
        rhs: SetExpr::Var(b),
    })
    .unwrap();
    for v in [a, b] {
        s.add_constraint(member(v, 1, true)).unwrap();
        s.add_constraint(card(v, 1)).unwrap();
    }
    assert!(s.check().is_err());
    assert!(s.get_model(a).is_none());
    assert!(s.check().is_err());
}

#[test]
fn f4_subset_and_compound_relations_reach_a_fixed_point() {
    let mut s = SetSolver::new();
    let ids: Vec<_> = (0..4)
        .map(|i| s.new_set_var(&format!("s{i}"), SetSort::IntSet))
        .collect();
    for pair in ids.windows(2).rev() {
        s.add_constraint(SetConstraint::Subset {
            lhs: SetExpr::Var(pair[0]),
            rhs: SetExpr::Var(pair[1]),
            sign: true,
        })
        .unwrap();
    }
    s.add_constraint(member(ids[0], 9, true)).unwrap();
    s.propagate().unwrap();
    assert!(s.get_var(ids[3]).unwrap().must_members.contains(&9));
    s.add_constraint(SetConstraint::Member {
        element: 9,
        sign: false,
        set: SetExpr::union(SetExpr::Var(ids[3]), SetExpr::Empty),
    })
    .unwrap();
    assert!(s.check().is_err());
}

#[test]
fn f4_negated_subset_requires_a_witness_and_cardinality_requires_a_model() {
    let mut s = SetSolver::new();
    let a = s.new_set_var("a", SetSort::IntSet);
    s.add_constraint(SetConstraint::Subset {
        lhs: SetExpr::Var(a),
        rhs: SetExpr::Var(a),
        sign: false,
    })
    .unwrap();
    assert!(s.check().is_err());
    s.reset();
    let a = s.new_set_var("a", SetSort::IntSet);
    s.add_constraint(card(a, 3)).unwrap();
    assert!(!s.check().unwrap());
    assert!(s.get_model(a).is_none());
}

#[test]
fn f4_membership_relations_and_notifications_are_trailed() {
    let mut s = SetSolver::new();
    let a = s.new_set_var("a", SetSort::IntSet);
    let b = s.new_set_var("b", SetSort::IntSet);
    s.register_term(t(1), a);
    s.register_term(t(2), b);
    s.add_constraint(member(a, 1, true)).unwrap();
    s.push();
    assert!(s.notify_equality(EqualityNotification {
        lhs: t(1),
        rhs: t(2),
        reason: Some(t(3))
    }));
    s.propagate().unwrap();
    assert!(s.get_var(b).unwrap().must_members.contains(&1));
    let temporary = s.new_set_var("temporary", SetSort::IntSet);
    s.register_term(t(4), temporary);
    s.pop();
    assert!(s.get_var_for_term(t(4)).is_none());
    assert!(s.get_var_by_name("temporary").is_none());
    s.add_constraint(member(b, 1, false)).unwrap();
    assert!(s.check().unwrap());
}

#[test]
fn f4_conflicts_and_extreme_cardinalities_are_scope_consistent() {
    let mut s = SetSolver::new();
    let a = s.new_set_var("a", SetSort::IntSet);
    s.push();
    s.add_constraint(member(a, 1, true)).unwrap();
    assert!(s.add_constraint(member(a, 1, false)).is_err());
    assert!(s.check().is_err());
    s.pop();
    assert!(s.check().unwrap());
    s.add_constraint(SetConstraint::Cardinality {
        set: SetExpr::Var(a),
        op: CardConstraintKind::Gt,
        bound: i64::MAX,
    })
    .unwrap();
    assert!(!s.check().unwrap());
}

#[test]
fn f5_opaque_assertions_never_certify_sat() {
    let mut s = SetSolver::new();
    s.push();
    assert!(matches!(s.assert_true(t(1)), Ok(TheoryResult::Unknown)));
    s.assert_false(t(1)).unwrap();
    assert!(matches!(Theory::check(&mut s), Ok(TheoryResult::Unknown)));
    s.pop();
    assert!(matches!(Theory::check(&mut s), Ok(TheoryResult::Sat)));
}

#[test]
fn f6_integer_parity_is_not_rational_feasibility() {
    for spfa in [false, true] {
        let mut s = ut(true, spfa);
        let x = s.get_or_create_var(t(1));
        s.add_sum(x, x, r(1), t(2));
        s.add_neg_sum(x, x, r(-1), t(3));
        assert!(matches!(s.check(), UtvpiResult::Conflict(_)));
        assert!(s.get_value(x).is_none());
        let mut s = ut(true, spfa);
        let x = s.get_or_create_var(t(1));
        s.add_neg_sum(x, x, r(-1), t(2));
        assert_eq!(s.check(), UtvpiResult::Ok);
        let x = s.get_value_exact(x).unwrap();
        assert!(x.is_integer() && x >= &BigRational::from_integer(1.into()));
    }
}

#[test]
fn f7_strict_constraints_and_fractional_integer_thresholds() {
    for spfa in [false, true] {
        let mut s = ut(false, spfa);
        let x = s.get_or_create_var(t(1));
        let mut c = UtConstraint::upper(x, r(0), t(2));
        c.strict = true;
        s.add_constraint(c);
        s.add_lower(x, r(0), t(3));
        assert!(matches!(s.check(), UtvpiResult::Conflict(_)));
        let mut s = ut(true, spfa);
        let x = s.get_or_create_var(t(1));
        let mut c = UtConstraint::upper(x, Rational64::new(1, 2), t(2));
        c.strict = true;
        s.add_constraint(c);
        s.add_lower(x, r(0), t(3));
        assert_eq!(s.check(), UtvpiResult::Ok);
        assert_eq!(s.get_value(x), Some(r(0)));
        let mut s = ut(false, spfa);
        let x = s.get_or_create_var(t(1));
        let mut lo = UtConstraint::lower(x, r(0), t(2));
        lo.strict = true;
        s.add_constraint(lo);
        let mut hi = UtConstraint::upper(x, Rational64::new(1, 1_000_000), t(3));
        hi.strict = true;
        s.add_constraint(hi);
        assert_eq!(s.check(), UtvpiResult::Ok);
        let v = s.get_value(x).unwrap();
        assert!(v > r(0) && v < Rational64::new(1, 1_000_000));
    }
}

#[test]
fn f7_weights_are_exact_beyond_i64() {
    let mut s = ut(true, true);
    let x = s.get_or_create_var(t(1));
    let mut c = UtConstraint::upper(x, r(i64::MIN), t(2));
    c.strict = true;
    s.add_constraint(c);
    assert_eq!(s.check(), UtvpiResult::Ok);
    assert!(s.get_value_exact(x).unwrap() < &BigRational::from_integer(i64::MIN.into()));
    assert!(s.get_value(x).is_none());
}

#[test]
fn f8_constant_constraints_and_strict_zero() {
    for spfa in [false, true] {
        for strict in [false, true] {
            let mut s = ut(false, spfa);
            let mut c = UtConstraint::new(
                0,
                Sign::Zero,
                0,
                Sign::Zero,
                r(if strict { 0 } else { -1 }),
                t(1),
            );
            c.strict = strict;
            s.add_constraint(c);
            assert!(matches!(s.check(), UtvpiResult::Conflict(_)));
        }
    }
}

#[test]
fn f9_synthetic_edges_survive_pop_and_checks_cover_every_component() {
    let mut graph = DoubledGraph::new(false);
    let x = graph.get_or_create_var(t(1));
    graph.push();
    graph.add_constraint(UtConstraint::upper(x, r(0), t(2)));
    graph.pop(1);
    assert_eq!(graph.get_edges(DoubledNode::SOURCE).count(), 2);
    for spfa in [false, true] {
        let mut s = ut(false, spfa);
        let x = s.get_or_create_var(t(1));
        s.push();
        s.add_upper(x, r(0), t(2));
        s.pop(1);
        s.add_upper(x, r(0), t(3));
        s.add_lower(x, r(-1), t(4));
        assert!(matches!(s.check(), UtvpiResult::Conflict(_)));
    }
}

#[test]
fn f10_bounds_are_entailed_not_arbitrary_potentials() {
    for spfa in [false, true] {
        let mut s = ut(false, spfa);
        let x = s.get_or_create_var(t(1));
        let y = s.get_or_create_var(t(2));
        assert_eq!(s.check(), UtvpiResult::Ok);
        assert_eq!(s.get_lower_bound(x), None);
        assert_eq!(s.get_upper_bound(x), None);
        s.add_diff(x, y, r(2), t(3));
        s.add_upper(y, r(5), t(4));
        s.add_lower(x, r(-3), t(5));
        assert_eq!(s.check(), UtvpiResult::Ok);
        assert_eq!(s.get_upper_bound(x), Some(r(7)));
        assert_eq!(s.get_lower_bound(x), Some(r(3)));
        s.push();
        assert!(s.get_value(x).is_none());
        s.pop(1);
        assert!(s.get_upper_bound(x).is_none());
    }
}

#[test]
fn f11_array_opaque_atoms_are_rejected_and_decoded_disequalities_work() {
    let mut s = ArraySolver::new();
    assert!(s.assert_false(t(10)).is_err());
    assert!(s.assert_true(t(11)).is_err());
    let a = s.intern(t(1));
    let b = s.intern(t(2));
    s.assert_diseq(a, b, t(12));
    assert!(matches!(s.check(), Ok(TheoryResult::Sat)));
}

#[test]
fn f12_array_undo_precedes_node_truncation() {
    let mut s = ArraySolver::new();
    let a = s.intern(t(1));
    s.push();
    let b = s.intern(t(2));
    s.merge(a, b, t(3)).unwrap();
    s.push();
    let c = s.intern(t(4));
    s.merge(b, c, t(5)).unwrap();
    s.pop();
    s.pop();
    let b = s.intern(t(2));
    assert!(!s.are_equal(a, b));
    s.assert_diseq(a, b, t(6));
    assert!(matches!(s.check(), Ok(TheoryResult::Sat)));
}

#[test]
fn f12_pending_array_axioms_survive_a_scoped_check() {
    let mut s = ArraySolver::new();
    let a = s.intern(t(1));
    let i = s.intern(t(2));
    let v = s.intern(t(3));
    let store = s.intern_store(t(4), a, i, v);
    let select = s.intern_select(t(5), store, i);
    s.push();
    s.check().unwrap();
    assert!(s.are_equal(select, v));
    s.pop();
    s.check().unwrap();
    assert!(s.are_equal(select, v));
}

#[test]
fn utvpi_both_engines_match_exhaustive_integer_oracle_and_validate_every_model() {
    let mut seed = 37u64;
    for _ in 0..250 {
        let mut constraints = Vec::new();
        for v in 0..2 {
            constraints.push(UtConstraint::upper(v, r(2), t(1)));
            constraints.push(UtConstraint::lower(v, r(2), t(1)));
        }
        for _ in 0..5 {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            let sign = |n: u64| match n % 3 {
                0 => Sign::Zero,
                1 => Sign::Positive,
                _ => Sign::Negative,
            };
            let mut c = UtConstraint::new(
                (seed % 2) as u32,
                sign(seed >> 2),
                ((seed >> 4) % 2) as u32,
                sign(seed >> 5),
                Rational64::new(((seed >> 8) % 9) as i64 - 4, 2),
                t(1),
            );
            c.strict = seed & (1 << 12) != 0;
            constraints.push(c);
        }
        let holds = |c: &UtConstraint, values: &[Rational64]| {
            let signed = |v: u32, s: Sign| match s {
                Sign::Zero => r(0),
                Sign::Positive => values[v as usize],
                Sign::Negative => -values[v as usize],
            };
            let lhs = signed(c.x, c.a) + signed(c.y, c.b);
            if c.strict {
                lhs < c.bound
            } else {
                lhs <= c.bound
            }
        };
        let feasible =
            (-2..=2).any(|x| (-2..=2).any(|y| constraints.iter().all(|c| holds(c, &[r(x), r(y)]))));
        for spfa in [false, true] {
            let mut s = ut(true, spfa);
            s.get_or_create_var(t(1));
            s.get_or_create_var(t(2));
            for c in &constraints {
                s.add_constraint(c.clone());
            }
            match s.check() {
                UtvpiResult::Ok => {
                    assert!(feasible);
                    let values = [s.get_value(0).unwrap(), s.get_value(1).unwrap()];
                    assert!(values.iter().all(|v| v.is_integer()));
                    assert!(constraints.iter().all(|c| holds(c, &values)));
                }
                UtvpiResult::Conflict(core) => {
                    assert!(!feasible);
                    assert!(!(-2..=2).any(|x| {
                        (-2..=2)
                            .any(|y| core.iter().all(|&i| holds(&constraints[i], &[r(x), r(y)])))
                    }));
                }
                UtvpiResult::Unknown => panic!("tiny integer oracle should be decided"),
            }
        }
    }
}

#[test]
fn arrangement_completeness_checks_transitivity_and_consistency() {
    use nixie_theories::combination::EqualityArrangement;
    let mut a = EqualityArrangement::new();
    assert!(a.is_complete(&[]));
    a.add_equality(t(1), t(2));
    a.add_equality(t(2), t(3));
    assert!(a.is_complete(&[t(1), t(2), t(3)]));
    a.add_disequality(t(1), t(3));
    assert!(!a.is_complete(&[t(1), t(2), t(3)]));
    let mut a = EqualityArrangement::new();
    for _ in 0..3 {
        a.add_equality(t(1), t(2));
    }
    assert!(!a.is_complete(&[t(1), t(2), t(3)]));
}

#[test]
fn f3_shared_conversion_engine_matches_ieee_native_casts() {
    use nixie_theories::fp::ieee754_full::{Ieee754Engine, convert_format};
    let mut seed = 67u64;
    let mut engine = Ieee754Engine::new();
    for _ in 0..512 {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        let x = f64::from_bits(seed);
        if !x.is_nan() {
            let value = convert_format(&mut engine, &FpValue::from_f64(x), FpFormat::FLOAT32);
            assert_eq!(
                value.to_f32().unwrap().to_bits(),
                (x as f32).to_bits(),
                "{x:?}"
            );
        }
        let x = f32::from_bits(seed as u32);
        if !x.is_nan() {
            let value = convert_format(&mut engine, &FpValue::from_f32(x), FpFormat::FLOAT64);
            assert_eq!(
                value.to_f64().unwrap().to_bits(),
                (x as f64).to_bits(),
                "{x:?}"
            );
        }
    }
}

#[test]
fn f3_identity_conversion_respects_abstract_nan_equality() {
    let mut s = FpSolver::new();
    let a = FpValue {
        sign: false,
        exponent: 255,
        significand: 1,
        format: FpFormat::FLOAT32,
    };
    let b = FpValue {
        sign: true,
        exponent: 255,
        significand: 2,
        format: FpFormat::FLOAT32,
    };
    s.assert_const(t(1), &a);
    s.assert_const(t(2), &b);
    s.assert_fp_to_fp(t(2), t(1), FpFormat::FLOAT32);
    assert!(matches!(s.check(), Ok(TheoryResult::Sat)));
}

#[test]
fn f4_finite_set_operations_match_exhaustive_two_element_semantics() {
    for left in 0u32..4 {
        for right in 0u32..4 {
            for operation in 0..3 {
                let expected = match operation {
                    0 => left | right,
                    1 => left & right,
                    _ => left & !right,
                };
                for wrong in [false, true] {
                    let mut s = SetSolver::new();
                    let a = s.new_set_var("a", SetSort::IntSet);
                    let b = s.new_set_var("b", SetSort::IntSet);
                    for (v, bits) in [(a, left), (b, right)] {
                        for e in 0..2 {
                            s.add_constraint(member(v, e, bits & (1 << e) != 0))
                                .unwrap();
                        }
                        s.add_constraint(card(v, bits.count_ones() as i64)).unwrap();
                    }
                    for e in 0..2 {
                        let expr = match operation {
                            0 => SetExpr::union(SetExpr::Var(a), SetExpr::Var(b)),
                            1 => SetExpr::intersection(SetExpr::Var(a), SetExpr::Var(b)),
                            _ => SetExpr::difference(SetExpr::Var(a), SetExpr::Var(b)),
                        };
                        s.add_constraint(SetConstraint::Member {
                            element: e,
                            set: expr,
                            sign: (expected & (1 << e) != 0) ^ (wrong && e == 0),
                        })
                        .unwrap();
                    }
                    let result = s.check();
                    if wrong {
                        assert!(result.is_err());
                    } else {
                        assert!(result.unwrap());
                    }
                }
            }
        }
    }
}

#[test]
fn fp_nan_constants_and_unary_operations_respect_abstract_equality() {
    let a = FpValue {
        sign: false,
        exponent: 255,
        significand: 1,
        format: FpFormat::FLOAT32,
    };
    let b = FpValue {
        sign: true,
        significand: 2,
        ..a
    };
    let mut constants = FpSolver::new();
    constants.assert_const(t(1), &a);
    constants.assert_const(t(1), &b);
    assert!(matches!(constants.check(), Ok(TheoryResult::Sat)));

    for nan in [true, false] {
        let mut unary = FpSolver::new();
        unary.assert_const(t(1), &if nan { a } else { FpValue::from_f32(1.0) });
        unary.assert_fp_neg(t(1), t(1));
        unary.assert_fp_abs(t(1), t(1));
        let result = unary.check().unwrap();
        if nan {
            assert!(matches!(result, TheoryResult::Sat));
        } else {
            assert!(matches!(result, TheoryResult::Unsat(_)));
        }
    }
}

#[test]
fn fp_unregistered_operands_do_not_silently_drop_constraints() {
    for operation in 0..13 {
        let mut s = FpSolver::new();
        match operation {
            0 => s.assert_is_nan(t(1)),
            1 => s.assert_is_infinite(t(1)),
            2 => s.assert_is_zero(t(1)),
            3 => s.assert_is_normal(t(1)),
            4 => s.assert_fp_eq(t(1), t(2)),
            5 => s.assert_fp_neg(t(1), t(2)),
            6 => s.assert_fp_abs(t(1), t(2)),
            7 => {
                s.assert_fp_ieee_eq(t(1), t(2));
            }
            8 => {
                s.assert_fp_lt(t(1), t(2));
            }
            9 => {
                s.assert_fp_le(t(1), t(2));
            }
            10 => s.assert_fp_to_sbv(t(1), t(2), 32),
            11 => s.assert_fp_to_ubv(t(1), t(2), 32),
            _ => s.assert_fp_to_real(t(1), t(2)),
        }
        assert!(
            matches!(s.check(), Ok(TheoryResult::Unknown)),
            "operation {operation}"
        );
    }
}
