//! Completeness regressions, independently checked against reference semantics.
#![allow(clippy::unwrap_used)]
use nixie_core::ast::TermId;
use nixie_theories::array::ArraySolver;
use nixie_theories::combination::{CombinationMode, TheoryCombiner};
use nixie_theories::fp::ieee754_full::{Ieee754Engine, convert_format};
use nixie_theories::fp::{FpFormat, FpRoundingMode, FpSolver, FpValue};
use nixie_theories::set::{
    CardConstraintKind as CK, SetConstraint as SC, SetExpr as SE, SetSolver, SetSort,
};

#[test]
fn array_registered_atoms_decode_both_polarities_and_follow_scopes() {
    let mut s = ArraySolver::new();
    s.register_equality_atom(term(100), term(1), term(2))
        .unwrap();
    assert!(matches!(s.assert_false(term(100)), Ok(TR::Sat)));
    s.push();
    assert!(matches!(s.assert_true(term(100)), Ok(TR::Unsat(_))));
    s.register_equality_atom(term(101), term(3), term(4))
        .unwrap();
    s.pop();
    assert!(matches!(s.check(), Ok(TR::Sat)));
    assert!(s.assert_false(term(101)).is_err());
    assert!(
        s.register_equality_atom(term(100), term(1), term(3))
            .is_err()
    );
    assert!(matches!(s.check(), Ok(TR::Sat)));
}

#[test]
fn decoded_set_assertions_have_sound_explanations_and_scoped_witnesses() {
    let mut s = SetSolver::new();
    let a = s.new_set_var("a", SetSort::IntSet);
    assert!(matches!(
        s.assert_decoded(
            term(100),
            SC::Cardinality {
                set: SE::Var(a),
                op: CK::Equal,
                bound: 1
            }
        ),
        Ok(TR::Sat)
    ));
    s.push();
    assert!(matches!(
        s.assert_decoded(
            term(101),
            SC::Member {
                element: 0,
                set: SE::Var(a),
                sign: true
            }
        ),
        Ok(TR::Sat)
    ));
    let result = s
        .assert_decoded(
            term(102),
            SC::Member {
                element: 1,
                set: SE::Var(a),
                sign: true,
            },
        )
        .unwrap();
    let TR::Unsat(core) = result else {
        panic!("decoded literals must explain their conflict");
    };
    assert_eq!(core, vec![term(100), term(101), term(102)]);
    s.pop();
    assert!(matches!(Theory::check(&mut s), Ok(TR::Sat)));
    s.push();
    s.get_var_mut(a).unwrap().must_members.extend([0, 1]);
    assert!(matches!(Theory::check(&mut s), Ok(TR::Unknown)));
    s.pop();
    assert!(matches!(Theory::check(&mut s), Ok(TR::Sat)));
}
use nixie_theories::{Theory, TheoryCheckResult as TR};
use num_rational::Rational64;

#[test]
fn sets_build_finite_and_cofinite_witnesses_and_restore_scopes() {
    let mut s = SetSolver::new();
    let a = s.new_set_var("a", SetSort::IntSet);
    let b = s.new_set_var("b", SetSort::IntSet);
    s.add_constraint(SC::Cardinality {
        set: SE::Var(a),
        op: CK::Equal,
        bound: 2,
    })
    .unwrap();
    s.add_constraint(SC::Equal {
        lhs: SE::Var(b),
        rhs: SE::Complement(Box::new(SE::Var(a))),
    })
    .unwrap();
    s.add_constraint(SC::Member {
        element: 0,
        set: SE::Var(a),
        sign: true,
    })
    .unwrap();
    s.add_constraint(SC::Member {
        element: 1,
        set: SE::Var(a),
        sign: false,
    })
    .unwrap();
    assert!(s.check().unwrap());
    assert_eq!(s.get_model(a).unwrap().len(), 2);
    assert!(s.get_model(b).is_none());
    let av = s.get_model_value(a).unwrap();
    let bv = s.get_model_value(b).unwrap();
    assert!(!av.default_member && bv.default_member);
    for e in 0..20 {
        assert_ne!(av.contains(e), bv.contains(e));
    }
    s.push();
    s.add_constraint(SC::Cardinality {
        set: SE::Var(b),
        op: CK::Le,
        bound: 3,
    })
    .unwrap();
    assert!(s.check().is_err());
    s.pop();
    assert!(s.get_model_value(b).is_none());
    assert!(s.check().unwrap());
}

#[test]
fn set_cardinality_and_negative_subset_match_exhaustive_finite_oracle() {
    for ca in 0..=2i64 {
        for cb in 0..=2i64 {
            for cu in 0..=4i64 {
                for disjoint in [false, true] {
                    for not_subset in [false, true] {
                        // At most four unnamed elements are needed for two sets of size
                        // at most two; six elements include the named 0 and 1 as well.
                        let expected = (0u32..64).any(|a| {
                            (0u32..64).any(|b| {
                                a.count_ones() as i64 == ca
                                    && b.count_ones() as i64 == cb
                                    && (a | b).count_ones() as i64 == cu
                                    && (!disjoint || a & b == 0)
                                    && (!not_subset || a & !b != 0)
                            })
                        });
                        let mut s = SetSolver::new();
                        let a = s.new_set_var("a", SetSort::IntSet);
                        let b = s.new_set_var("b", SetSort::IntSet);
                        for (v, bound) in [(a, ca), (b, cb)] {
                            s.add_constraint(SC::Cardinality {
                                set: SE::Var(v),
                                op: CK::Equal,
                                bound,
                            })
                            .unwrap();
                        }
                        s.add_constraint(SC::Cardinality {
                            set: SE::union(SE::Var(a), SE::Var(b)),
                            op: CK::Equal,
                            bound: cu,
                        })
                        .unwrap();
                        if disjoint {
                            s.add_constraint(SC::Disjoint {
                                lhs: SE::Var(a),
                                rhs: SE::Var(b),
                            })
                            .unwrap();
                        }
                        if not_subset {
                            s.add_constraint(SC::Subset {
                                lhs: SE::Var(a),
                                rhs: SE::Var(b),
                                sign: false,
                            })
                            .unwrap();
                        }
                        let result = s.check();
                        if expected {
                            assert!(result.unwrap(), "{ca} {cb} {cu} {disjoint} {not_subset}");
                            let a = s.get_model(a).unwrap();
                            let b = s.get_model(b).unwrap();
                            assert_eq!(a.len() as i64, ca);
                            assert_eq!(b.len() as i64, cb);
                            assert_eq!(a.union(&b).count() as i64, cu);
                            assert!(!disjoint || a.is_disjoint(&b));
                            assert!(!not_subset || !a.is_subset(&b));
                        } else {
                            assert!(result.is_err(), "{ca} {cb} {cu} {disjoint} {not_subset}");
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn universal_and_complement_are_checked_beyond_named_elements() {
    let mut s = SetSolver::new();
    let a = s.new_set_var("a", SetSort::IntSet);
    s.add_constraint(SC::Equal {
        lhs: SE::Var(a),
        rhs: SE::Universal,
    })
    .unwrap();
    assert!(s.check().unwrap());
    let model = s.get_model_value(a).unwrap();
    assert!(model.default_member && model.exceptions.is_empty());
    s.push();
    s.add_constraint(SC::Equal {
        lhs: SE::Var(a),
        rhs: SE::Complement(Box::new(SE::Var(a))),
    })
    .unwrap();
    assert!(s.check().is_err());
    s.pop();
    assert!(s.check().unwrap());
}

fn term(n: u32) -> TermId {
    TermId::new(n)
}

#[test]
fn arrangement_search_finds_an_alternative_and_never_commits_assumptions() {
    for mode in [CombinationMode::Polite, CombinationMode::ModelBased] {
        let mut c = TheoryCombiner::with_mode(mode);
        for v in [term(10), term(20), term(30)] {
            c.add_shared_var(v);
            c.arith_mut().intern(v);
        }
        let a = c.euf_mut().intern(term(10));
        let b = c.euf_mut().intern(term(20));
        let d = c.euf_mut().intern(term(30));
        c.euf_mut().assert_diseq(a, b, term(100));
        c.euf_mut().assert_diseq(a, d, term(101));
        c.euf_mut().assert_diseq(b, d, term(102));
        assert!(matches!(c.check(), Ok(TR::Sat)));
        let values: Vec<_> = [term(10), term(20), term(30)]
            .iter()
            .map(|&v| c.shared_value(v).unwrap().clone())
            .collect();
        assert!(values[0] != values[1] && values[1] != values[2] && values[0] != values[2]);
        c.push();
        // Force the opposite order to the chosen candidate. A retained branch
        // would spuriously refute this satisfiable extension.
        for (v, value) in [(term(10), 3), (term(20), 2), (term(30), 1)] {
            c.arith_mut().assert_eq(
                &[(v, Rational64::from_integer(1))],
                Rational64::from_integer(value),
                term(200 + value as u32),
            );
        }
        assert!(matches!(c.check(), Ok(TR::Sat)));
        c.pop();
        assert!(c.shared_value(term(10)).is_none());
        assert!(matches!(c.check(), Ok(TR::Sat)));
    }
}

#[test]
fn arrangement_refutation_exhausts_all_orders_and_excludes_branch_reasons() {
    for mode in [CombinationMode::Polite, CombinationMode::ModelBased] {
        let mut c = TheoryCombiner::with_mode(mode);
        for (v, reason) in [(term(10), term(100)), (term(20), term(200))] {
            c.add_shared_var(v);
            c.arith_mut().assert_eq(
                &[(v, Rational64::from_integer(1))],
                Rational64::from_integer(0),
                reason,
            );
        }
        let a = c.euf_mut().intern(term(10));
        let b = c.euf_mut().intern(term(20));
        c.push();
        c.euf_mut().assert_diseq(a, b, term(300));
        let TR::Unsat(core) = c.check().unwrap() else {
            panic!("all arrangements must be refuted");
        };
        assert!(
            core.iter()
                .all(|v| [term(100), term(200), term(300)].contains(v))
        );
        assert!(core.contains(&term(300)));
        c.pop();
        assert!(matches!(c.check(), Ok(TR::Sat)));
    }
}

fn symbolic_conversion(value: FpValue, target: FpFormat, mode: FpRoundingMode) -> FpValue {
    let mut engine = Ieee754Engine::new();
    engine.set_rounding_mode(mode);
    let expected = convert_format(&mut engine, &value, target);
    let mut s = FpSolver::new();
    s.set_rounding_mode(mode);
    s.new_fp(term(1), value.format);
    // Encode BEFORE asserting constants: this exercises the symbolic circuit.
    s.assert_fp_to_fp(term(2), term(1), target);
    s.assert_const(term(1), &value);
    assert!(
        matches!(s.check(), Ok(TR::Sat)),
        "{value:?} {target:?} {mode:?}"
    );
    let actual = s.get_value(term(2)).unwrap();
    assert!(
        actual == expected || (actual.is_nan() && expected.is_nan()),
        "{value:?} {target:?} {mode:?}: {actual:?} != {expected:?}"
    );
    s.push();
    let wrong = if expected.is_zero() {
        FpValue::pos_infinity(target)
    } else {
        FpValue::pos_zero(target)
    };
    s.assert_const(term(2), &wrong);
    assert!(matches!(s.check(), Ok(TR::Unsat(_))));
    s.pop();
    assert!(matches!(s.check(), Ok(TR::Sat)));
    actual
}

#[test]
#[ignore = "requires the installed Z3 semantic oracle"]
fn symbolic_fp_circuits_match_z3_exhaustively() {
    use std::io::Write;
    use std::process::{Command, Stdio};
    let version = Command::new("z3").arg("--version").output().unwrap();
    assert!(version.status.success());
    eprintln!("{}", String::from_utf8_lossy(&version.stdout).trim());
    let numeral = |v: FpValue| {
        format!(
            "(fp #b{} (_ bv{} {}) (_ bv{} {}))",
            u8::from(v.sign),
            v.exponent,
            v.format.exponent_bits,
            v.significand,
            v.format.significand_bits - 1
        )
    };
    let mut script = String::from("(set-logic QF_FP)\n");
    let mut cases = 0;
    for source in [FpFormat::new(3, 4), FpFormat::new(2, 5)] {
        for target in [FpFormat::new(2, 3), FpFormat::new(4, 5)] {
            for (mode, rm) in [
                (FpRoundingMode::RoundNearestTiesToEven, "RNE"),
                (FpRoundingMode::RoundNearestTiesToAway, "RNA"),
                (FpRoundingMode::RoundTowardPositive, "RTP"),
                (FpRoundingMode::RoundTowardNegative, "RTN"),
                (FpRoundingMode::RoundTowardZero, "RTZ"),
            ] {
                for raw in 0..(1u64 << source.width()) {
                    let value = FpValue {
                        sign: raw >> (source.width() - 1) != 0,
                        exponent: (raw >> (source.significand_bits - 1))
                            & ((1 << source.exponent_bits) - 1),
                        significand: raw & ((1 << (source.significand_bits - 1)) - 1),
                        format: source,
                    };
                    let actual = symbolic_conversion(value, target, mode);
                    script.push_str(&format!("(push)\n(assert (not (= ((_ to_fp {} {}) {rm} {}) {})))\n(check-sat)\n(pop)\n",
                        target.exponent_bits, target.significand_bits, numeral(value), numeral(actual)));
                    cases += 1;
                }
            }
        }
    }
    let mut child = Command::new("z3")
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let writer = std::thread::spawn(move || stdin.write_all(script.as_bytes()));
    let result = child.wait_with_output().unwrap();
    writer.join().unwrap().unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let output = String::from_utf8(result.stdout).unwrap();
    assert_eq!(output.lines().count(), cases);
    assert!(output.lines().all(|line| line == "unsat"), "{output}");
    eprintln!("{cases} symbolic conversion results independently agree with Z3");
}

#[test]
fn symbolic_fp_conversion_exhausts_small_formats_and_rounding_modes() {
    for source in [FpFormat::new(3, 4), FpFormat::new(2, 5)] {
        for target in [FpFormat::new(2, 3), FpFormat::new(4, 5)] {
            for mode in [
                FpRoundingMode::RoundNearestTiesToEven,
                FpRoundingMode::RoundNearestTiesToAway,
                FpRoundingMode::RoundTowardPositive,
                FpRoundingMode::RoundTowardNegative,
                FpRoundingMode::RoundTowardZero,
            ] {
                for raw in 0..(1u64 << source.width()) {
                    symbolic_conversion(
                        FpValue {
                            sign: raw >> (source.width() - 1) != 0,
                            exponent: (raw >> (source.significand_bits - 1))
                                & ((1 << source.exponent_bits) - 1),
                            significand: raw & ((1 << (source.significand_bits - 1)) - 1),
                            format: source,
                        },
                        target,
                        mode,
                    );
                }
            }
        }
    }
}

#[test]
fn symbolic_fp_binary128_models_preserve_bits_above_u64() {
    let mut s = FpSolver::new();
    for (source, target, value) in [(term(1), term(2), 1.5), (term(3), term(4), 1.25)] {
        s.new_fp(source, FpFormat::FLOAT64);
        s.assert_fp_to_fp(target, source, FpFormat::FLOAT128);
        s.assert_const(source, &FpValue::from_f64(value));
    }
    s.assert_fp_to_fp(term(5), term(2), FpFormat::FLOAT32);
    assert!(matches!(s.check(), Ok(TR::Sat)));
    let exact = s.get_value_exact(term(2)).unwrap();
    assert_eq!(exact.exponent, num_bigint::BigUint::from(16383u32));
    assert_eq!(
        exact.significand,
        num_bigint::BigUint::from(1u8) << 111usize
    );
    assert_eq!(s.get_value(term(5)), Some(FpValue::from_f32(1.5)));
    assert!(s.get_value(term(2)).is_none());
    let model = s.get_model();
    let a = model.iter().find(|(t, _)| *t == term(2)).unwrap().1;
    let b = model.iter().find(|(t, _)| *t == term(4)).unwrap().1;
    assert_ne!(a, b);
    s.push();
    s.assert_fp_eq(term(2), term(4));
    assert!(matches!(s.check(), Ok(TR::Unsat(_))));
    assert!(s.get_value_exact(term(2)).is_none());
    s.pop();
    assert!(matches!(s.check(), Ok(TR::Sat)));
}

#[test]
fn symbolic_fp_standard_formats_cover_subnormals_ties_and_overflow() {
    for raw in [
        0,
        1,
        0x007f_ffff,
        0x0080_0000,
        0x3f80_0000,
        0x7f7f_ffff,
        0x7f80_0000,
        0x7fc0_0001,
        0x8000_0000,
        0xff7f_ffff,
    ] {
        for target in [FpFormat::FLOAT16, FpFormat::FLOAT64] {
            for mode in [
                FpRoundingMode::RoundNearestTiesToEven,
                FpRoundingMode::RoundNearestTiesToAway,
                FpRoundingMode::RoundTowardPositive,
                FpRoundingMode::RoundTowardNegative,
                FpRoundingMode::RoundTowardZero,
            ] {
                symbolic_conversion(FpValue::from_f32(f32::from_bits(raw)), target, mode);
            }
        }
    }
    for raw in [
        1,
        0x380f_ffff_ffff_ffff,
        0x3810_0000_0000_0000,
        0x3ff0_0000_1000_0000,
        0x47ef_ffff_ffff_ffff,
        0x7fef_ffff_ffff_ffff,
    ] {
        for mode in [
            FpRoundingMode::RoundNearestTiesToEven,
            FpRoundingMode::RoundNearestTiesToAway,
            FpRoundingMode::RoundTowardPositive,
            FpRoundingMode::RoundTowardNegative,
            FpRoundingMode::RoundTowardZero,
        ] {
            symbolic_conversion(
                FpValue::from_f64(f64::from_bits(raw)),
                FpFormat::FLOAT32,
                mode,
            );
        }
    }
}
