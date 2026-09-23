//! Constructed standalone theory workloads; see bench/theory_perf/README.md.
use nixie_core::ast::TermId;
use nixie_theories::array::ArraySolver;
use nixie_theories::combination::{CombinationMode, TheoryCombiner};
use nixie_theories::fp::ieee754_full::{Ieee754Engine, convert_format};
use nixie_theories::fp::{FpFormat, FpRoundingMode, FpSolver, FpValue};
use nixie_theories::set::{CardConstraintKind, SetConstraint, SetExpr, SetSolver, SetSort};
use nixie_theories::{Theory, TheoryCheckResult as TR};
use num_rational::Rational64;
use std::error::Error;

fn term(n: usize) -> TermId {
    TermId::new(n as u32)
}

fn value(v: FpValue) -> String {
    format!(
        "(fp #b{} (_ bv{} {}) (_ bv{} {}))",
        u8::from(v.sign),
        v.exponent,
        v.format.exponent_bits,
        v.significand,
        v.format.significand_bits - 1
    )
}

fn fp(family: &str, count: usize, seed: usize, emit: bool) -> Result<(), Box<dyn Error>> {
    let (source, target) = match family {
        "fp16-32" => (FpFormat::new(5, 11), FpFormat::new(8, 24)),
        "fp32-16" => (FpFormat::new(8, 24), FpFormat::new(5, 11)),
        "fp64-32" => (FpFormat::new(11, 53), FpFormat::new(8, 24)),
        _ => return Err("unknown FP family".into()),
    };
    let (mode, rm) = [
        (FpRoundingMode::RoundNearestTiesToEven, "RNE"),
        (FpRoundingMode::RoundNearestTiesToAway, "RNA"),
        (FpRoundingMode::RoundTowardPositive, "RTP"),
        (FpRoundingMode::RoundTowardNegative, "RTN"),
        (FpRoundingMode::RoundTowardZero, "RTZ"),
    ][seed % 5];
    let mut engine = Ieee754Engine::new();
    engine.set_rounding_mode(mode);
    let mut s = FpSolver::new();
    s.set_rounding_mode(mode);
    let mut expected = Vec::new();
    if emit {
        println!("(set-logic QF_FP)");
    }
    for i in 0..count {
        let exponent = match (seed + i) % 5 {
            0 => 0,
            1 => (1 << source.exponent_bits) - 1,
            2 => 1,
            3 => (1 << (source.exponent_bits - 1)) - 1,
            _ => (1 << source.exponent_bits) - 2,
        };
        let input = FpValue {
            format: source,
            sign: !(seed + i).is_multiple_of(2),
            exponent,
            significand: ((seed as u64 + 1) * 0x123456789 + i as u64)
                & ((1u64 << (source.significand_bits - 1)) - 1),
        };
        let output = convert_format(&mut engine, &input, target);
        expected.push(output);
        if emit {
            println!(
                "(declare-const x{i} (_ FloatingPoint {} {}))",
                source.exponent_bits, source.significand_bits
            );
            println!(
                "(declare-const y{i} (_ FloatingPoint {} {}))",
                target.exponent_bits, target.significand_bits
            );
            println!(
                "(assert (= y{i} ((_ to_fp {} {}) {rm} x{i})))",
                target.exponent_bits, target.significand_bits
            );
            println!("(assert (= x{i} {}))", value(input));
        } else {
            s.new_fp(term(2 * i + 1), source);
            s.assert_fp_to_fp(term(2 * i + 2), term(2 * i + 1), target);
            s.assert_const(term(2 * i + 1), &input);
        }
    }
    for round in 0..2 {
        if emit {
            println!("(check-sat)");
            println!(
                "(get-value ({}))",
                expected
                    .iter()
                    .enumerate()
                    .map(|(i, v)| format!("(= y{i} {})", value(*v)))
                    .collect::<Vec<_>>()
                    .join(" ")
            );
        } else {
            assert!(matches!(s.check()?, TR::Sat));
            for (i, expected) in expected.iter().enumerate() {
                let actual = s.get_value(term(2 * i + 2)).ok_or("missing FP witness")?;
                assert!(actual == *expected || actual.is_nan() && expected.is_nan());
            }
        }
        if round == 0 {
            let wrong = if expected[0].is_zero() {
                FpValue::pos_infinity(target)
            } else {
                FpValue::pos_zero(target)
            };
            if emit {
                println!(
                    "(push 1)\n(assert (= y0 {}))\n(check-sat)\n(pop 1)",
                    value(wrong)
                );
            } else {
                s.push();
                s.assert_const(term(2), &wrong);
                assert!(matches!(s.check()?, TR::Unsat(_)));
                s.pop();
            }
        }
    }
    Ok(())
}

fn sets(count: usize, seed: usize, emit: bool) -> Result<(), Box<dyn Error>> {
    let mut s = SetSolver::new();
    let a = s.new_set_var("a", SetSort::IntSet);
    let b = s.new_set_var("b", SetSort::IntSet);
    let members: Vec<_> = (0..count)
        .map(|i| ((i + seed) % count + seed * 100) as u32)
        .collect();
    if emit {
        println!(
            "(set-logic ALL)\n(declare-const a (Array Int Bool))\n(declare-const b (Array Int Bool))"
        );
        let mut array = "((as const (Array Int Bool)) false)".to_owned();
        for e in &members {
            array = format!("(store {array} {e} true)");
        }
        println!("(assert (= a {array}))\n(assert (= b ((_ map not) a)))");
    } else {
        s.add_constraint(SetConstraint::Equal {
            lhs: SetExpr::Var(b),
            rhs: SetExpr::Complement(Box::new(SetExpr::Var(a))),
        })
        .map_err(|e| format!("{e:?}"))?;
        s.add_constraint(SetConstraint::Cardinality {
            set: SetExpr::Var(a),
            op: CardConstraintKind::Equal,
            bound: count as i64,
        })
        .map_err(|e| format!("{e:?}"))?;
        for &element in &members {
            s.add_constraint(SetConstraint::Member {
                element,
                set: SetExpr::Var(a),
                sign: true,
            })
            .map_err(|e| format!("{e:?}"))?;
        }
    }
    for round in 0..2 {
        if emit {
            println!(
                "(check-sat)\n(get-value ((= b ((_ map not) a)) {}))",
                members
                    .iter()
                    .map(|e| format!("(select a {e})"))
                    .collect::<Vec<_>>()
                    .join(" ")
            );
        } else {
            assert!(s.check().map_err(|e| format!("{e:?}"))?);
            let av = s.get_model_value(a).ok_or("missing finite witness")?;
            let bv = s.get_model_value(b).ok_or("missing cofinite witness")?;
            assert!(!av.default_member && bv.default_member);
            assert_eq!(av.exceptions.len(), count);
            assert_eq!(av.exceptions, bv.exceptions);
            assert!(members.iter().all(|&e| av.contains(e) && !bv.contains(e)));
        }
        if round == 0 {
            if emit {
                println!(
                    "(push 1)\n(assert (select b {}))\n(check-sat)\n(pop 1)",
                    members[0]
                );
            } else {
                s.push();
                let result = s.add_constraint(SetConstraint::Member {
                    element: members[0],
                    set: SetExpr::Var(b),
                    sign: true,
                });
                assert!(result.is_err() || s.check().is_err());
                s.pop();
            }
        }
    }
    Ok(())
}

fn arrangements(count: usize, seed: usize, emit: bool) -> Result<(), Box<dyn Error>> {
    let mut c = TheoryCombiner::with_mode(CombinationMode::Polite);
    let order: Vec<_> = (0..count).map(|i| (i + seed) % count).collect();
    if emit {
        println!("(set-logic QF_UFLRA)");
    }
    for &i in &order {
        if emit {
            println!("(declare-const x{i} Real)");
        } else {
            c.add_shared_var(term(i + 1));
            c.arith_mut().intern(term(i + 1));
        }
    }
    for i in 0..count {
        for j in 0..i {
            if emit {
                println!("(assert (distinct x{i} x{j}))");
            } else {
                let a = c.euf_mut().intern(term(i + 1));
                let b = c.euf_mut().intern(term(j + 1));
                c.euf_mut().assert_diseq(a, b, term(1000 + i * count + j));
            }
        }
    }
    for round in 0..2 {
        if emit {
            println!(
                "(check-sat)\n(get-value ({}))",
                (0..count)
                    .map(|i| format!("x{i}"))
                    .collect::<Vec<_>>()
                    .join(" ")
            );
        } else {
            assert!(matches!(c.check()?, TR::Sat));
            let values: Vec<_> = (0..count)
                .map(|i| c.shared_value(term(i + 1)).ok_or("missing shared witness"))
                .collect::<Result<_, _>>()?;
            for i in 0..count {
                for j in 0..i {
                    assert_ne!(values[i], values[j]);
                }
            }
        }
        if round == 0 {
            if emit {
                println!("(push 1)\n(assert (= x0 0))\n(assert (= x1 0))\n(check-sat)\n(pop 1)");
            } else {
                c.push();
                for i in 1..=2 {
                    c.arith_mut().assert_eq(
                        &[(term(i), Rational64::from_integer(1))],
                        Rational64::from_integer(0),
                        term(5000 + i),
                    );
                }
                assert!(matches!(c.check()?, TR::Unsat(_)));
                c.pop();
            }
        }
    }
    Ok(())
}

fn arrays(count: usize, seed: usize, emit: bool) -> Result<(), Box<dyn Error>> {
    let mut s = ArraySolver::new();
    let order: Vec<_> = (0..count).map(|i| (i + seed) % count).collect();
    if emit {
        println!("(set-logic QF_AUFLIA)");
    }
    for &i in &order {
        if emit {
            println!("(declare-const a{i} (Array Int Int))");
        } else {
            s.intern_array(term(i + 1));
        }
    }
    for i in 1..count {
        if emit {
            println!("(assert (= a{} a{i}))", i - 1);
        } else {
            s.register_equality_atom(term(1000 + i), term(i), term(i + 1))?;
            assert!(matches!(s.assert_true(term(1000 + i))?, TR::Sat));
        }
    }
    if !emit {
        s.register_equality_atom(term(5000), term(1), term(count))?;
    }
    for round in 0..2 {
        if emit {
            println!(
                "(check-sat)\n(get-value ({}))",
                (1..count)
                    .map(|i| format!("(= a0 a{i})"))
                    .collect::<Vec<_>>()
                    .join(" ")
            );
        } else {
            assert!(matches!(s.check()?, TR::Sat));
            assert!((1..count).all(|i| s.are_terms_equal(term(1), term(i + 1))));
        }
        if round == 0 {
            if emit {
                println!(
                    "(push 1)\n(assert (distinct a0 a{}))\n(check-sat)\n(pop 1)",
                    count - 1
                );
            } else {
                s.push();
                assert!(matches!(s.assert_false(term(5000))?, TR::Unsat(_)));
                s.pop();
            }
        }
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<_> = std::env::args().collect();
    if args.len() != 5 {
        return Err("usage: audited-theory-perf FAMILY COUNT SEED solve|emit".into());
    }
    let count: usize = args[2].parse()?;
    let seed: usize = args[3].parse()?;
    if !(1..=256).contains(&count) || seed > 1000 {
        return Err("invalid benchmark dimensions".into());
    }
    let emit = match args[4].as_str() {
        "emit" => true,
        "solve" => false,
        _ => return Err("invalid mode".into()),
    };
    match args[1].as_str() {
        "fp16-32" | "fp32-16" | "fp64-32" => fp(&args[1], count, seed, emit)?,
        "sets" => sets(count, seed, emit)?,
        "arrangements" if count >= 2 => arrangements(count, seed, emit)?,
        "arrays" if count >= 2 => arrays(count, seed, emit)?,
        _ => return Err("unknown family/dimension".into()),
    }
    if emit {
        println!("(exit)");
    } else {
        println!("sat\nunsat\nsat");
    }
    Ok(())
}
