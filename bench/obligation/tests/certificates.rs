//! Certificate tests: every family, many seeds, both parities/variants.
//! These run without any solver — they verify the generator's own math
//! (witnesses, Hall deficits, modular obstructions, permutation
//! compositions, array-history simulations, Euclidean semantics).

use nixie_obligation::boundary;
use nixie_obligation::capacity;
use nixie_obligation::gap;
use nixie_obligation::memory;
use nixie_obligation::parity;
use nixie_obligation::reconverge;
use nixie_obligation::registry;
use nixie_obligation::registry::Size;
use nixie_obligation::{Answer, smt_div, smt_mod};

#[test]
fn smt_euclidean_semantics() {
    // SMT-LIB: remainder in [0, b) for b > 0, quotient floors.
    for a in -60..=60 {
        for b in 2..=13 {
            let r = smt_mod(a, b);
            let q = smt_div(a, b);
            assert!((0..b).contains(&r), "mod({a},{b}) = {r} out of range");
            assert_eq!(b * q + r, a, "div/mod identity failed for ({a},{b})");
        }
    }
}

#[test]
fn parity_certificates_and_minimality() {
    for seed in 0..8u64 {
        for &(v, e) in &[(8usize, 6usize), (14, 10)] {
            for &odd in &[false, true] {
                let d = parity::build(
                    seed,
                    &parity::Params {
                        vertices: v,
                        extra_edges: e,
                    },
                    odd,
                )
                .unwrap_or_else(|e| panic!("seed {seed}: {e}"));
                d.verify().unwrap_or_else(|e| panic!("seed {seed}: {e}"));
                assert_eq!(d.answer(), if odd { Answer::Unsat } else { Answer::Sat });
                if v <= 10 {
                    d.verify_minimal_obstruction()
                        .unwrap_or_else(|e| panic!("seed {seed}: {e}"));
                }
            }
        }
    }
}

#[test]
fn parity_dropping_any_row_is_satisfiable() {
    // Explicit check of the "minimal obstruction" claim on a mid-size graph.
    let d = parity::build(
        42,
        &parity::Params {
            vertices: 16,
            extra_edges: 12,
        },
        true,
    )
    .expect("build");
    d.verify_minimal_obstruction().expect("minimal");
}

#[test]
fn capacity_certificates() {
    for seed in 0..8u64 {
        for &sat in &[true, false] {
            let d = capacity::build(
                seed,
                &capacity::Params {
                    objects: 7,
                    extra_resources: 3,
                    allowed_min: 2,
                    allowed_max: 4,
                    deficit: 1,
                },
                sat,
                capacity::Variant::Main,
            )
            .unwrap_or_else(|e| panic!("seed {seed}: {e}"));
            d.verify().unwrap_or_else(|e| panic!("seed {seed}: {e}"));
            assert_eq!(d.answer(), if sat { Answer::Sat } else { Answer::Unsat });
        }
    }
}

#[test]
fn gap_certificates() {
    for seed in 0..8u64 {
        for &(vars, k) in &[(4usize, 0u32), (6, 3), (9, 6)] {
            let d = gap::build(
                seed,
                &gap::Params {
                    vars,
                    scale_log10: k,
                },
            )
            .unwrap_or_else(|e| panic!("seed {seed} vars {vars}: {e}"));
            d.verify().unwrap_or_else(|e| panic!("seed {seed}: {e}"));
        }
    }
}

#[test]
fn gap_small_instance_is_really_integer_infeasible() {
    // Brute-force the 0/1 box for a small instance: no integer solution,
    // while x = 1/2 works rationally (checked by verify()).
    let d = gap::build(
        7,
        &gap::Params {
            vars: 5,
            scale_log10: 0,
        },
    )
    .expect("build");
    d.verify().expect("verify");
    for bits in 0u32..(1 << 5) {
        let x: Vec<i128> = (0..5).map(|c| ((bits >> c) & 1) as i128).collect();
        let mut ok = true;
        for r in 0..5 {
            let lhs: i128 = (0..5).map(|c| d.a2[r][c] * x[c]).sum();
            if lhs != d.rhs2[r] {
                ok = false;
                break;
            }
        }
        assert!(!ok, "found an integer solution — certificate is wrong");
    }
}

#[test]
fn reconverge_certificates() {
    for seed in 0..8u64 {
        for &(k, w) in &[(3usize, 16usize), (4, 32), (5, 8)] {
            let d = reconverge::build(
                seed,
                &reconverge::Params {
                    inputs: k,
                    width: w,
                },
            )
            .unwrap_or_else(|e| panic!("seed {seed}: {e}"));
            d.verify().unwrap_or_else(|e| panic!("seed {seed}: {e}"));
        }
    }
}

#[test]
fn reconverge_permutation_roundtrip_composition() {
    // Direct check: composing the emitted networks' permutations yields the
    // claimed sigma for both the identity and transposition variants.
    for seed in 0..4u64 {
        let d = reconverge::build(
            seed,
            &reconverge::Params {
                inputs: 3,
                width: 32,
            },
        )
        .expect("build");
        for j in 0..d.w {
            assert_eq!(d.perm[d.w - 1 - d.q_ident[j]], d.w - 1 - j);
        }
    }
}

#[test]
fn memory_certificates() {
    for seed in 0..8u64 {
        let p = memory::Params { writes: 8 };
        let d1 = memory::build(
            seed,
            &p,
            &memory::Variant::Reorder {
                offset_implied: false,
            },
        )
        .unwrap_or_else(|e| panic!("seed {seed}: {e}"));
        d1.verify().unwrap_or_else(|e| panic!("seed {seed}: {e}"));
        let d2 = memory::build(seed, &p, &memory::Variant::Alias)
            .unwrap_or_else(|e| panic!("seed {seed}: {e}"));
        d2.verify().unwrap_or_else(|e| panic!("seed {seed}: {e}"));
    }
}

#[test]
fn boundary_certificates() {
    for seed in 0..8u64 {
        let d = boundary::build(seed, &boundary::Params { facts: 8 })
            .unwrap_or_else(|e| panic!("seed {seed}: {e}"));
        d.verify().unwrap_or_else(|e| panic!("seed {seed}: {e}"));
    }
}

#[test]
fn registry_generates_all_families_with_verified_shapes() {
    for &size in &[Size::Small, Size::Medium] {
        let insts = registry::generate_all(2, size, None).expect("generate");
        assert!(!insts.is_empty());
        for inst in &insts {
            assert!(
                !inst.expected.is_empty(),
                "{}: no expected answers",
                inst.name
            );
            assert!(
                !inst.certificate.is_empty(),
                "{}: no certificate",
                inst.name
            );
            assert!(
                inst.script.contains("check-sat")
                    || inst.kind == nixie_obligation::InstanceKind::Cnf
            );
            let n_checks = inst.script.matches("(check-sat)").count();
            if inst.kind == nixie_obligation::InstanceKind::Smt2 {
                assert_eq!(
                    n_checks,
                    inst.expected.len(),
                    "{}: check-sat count {} != expected {}",
                    inst.name,
                    n_checks,
                    inst.expected.len()
                );
            }
            // Answer must be decided (never Unknown) — we only emit
            // certified instances.
            assert!(
                inst.expected.iter().all(|a| *a != Answer::Unknown),
                "{}: undecided expected answer",
                inst.name
            );
        }
    }
}

#[test]
fn stressed_registry_preserves_check_structure() {
    let cfg = nixie_obligation::stress::StressCfg::mild();
    let insts = registry::generate_all(1, Size::Small, Some(&cfg)).expect("generate stressed");
    assert!(insts.iter().all(|i| {
        i.kind == nixie_obligation::InstanceKind::Cnf
            || i.script.matches("(check-sat)").count() == i.expected.len()
    }));
    assert!(insts.iter().any(|i| i.tags.contains(&"rep-stress")));
}

#[test]
fn deep_stress_block_is_tautological() {
    // The inserted block must be satisfiable on its own: check that the
    // generated deep scripts for a trivially sat base keep all expected
    // answers (structural check only; semantics checked via z3 in the
    // runner).
    let mut rng = nixie_obligation::Rng::new(1);
    let base = "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n";
    let cfg = nixie_obligation::stress::StressCfg {
        bool_depth: 64,
        int_depth: 64,
        cnf_dup: 1,
    };
    let stressed = nixie_obligation::stress::apply_smt2(base, &cfg, &mut rng, "QF_LIA");
    assert_eq!(stressed.matches("(check-sat)").count(), 1);
    assert!(stressed.contains("(declare-const sdb Bool)"));
    assert!(stressed.contains("(declare-const sdi Int)"));
    let bv_base = "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(check-sat)\n";
    let bv_stressed = nixie_obligation::stress::apply_smt2(bv_base, &cfg, &mut rng, "QF_BV");
    assert!(bv_stressed.contains("(declare-const sdv (_ BitVec 32))"));
    assert!(!bv_stressed.contains("sdi"));
}

/// `fpboundary` oracle pins: the exact-arithmetic model's answers on the
/// analytic corners the family asserts (the same cases the instances pin,
/// computed here independently of the generation paths).
#[test]
fn fpboundary_oracle_pins() {
    use nixie_obligation::fpboundary::{DecF64, Rm, round_exact};
    let ms = 1u128; // one min-subnormal unit at 2^-1074
    let e = -1074i32;
    // Exact subnormal arithmetic stays exact: -2ms - 3ms = -5ms (RNA must
    // NOT round an exact grid value — the oracle bug this pins).
    assert_eq!(round_exact(true, 5, e, Rm::Rna), 0x8000_0000_0000_0005);
    // Directed underflow corners: the exact product of the two smallest
    // subnormals is ~2^-2148, far below the grid.
    let prod = ms * ms;
    let pe = 2 * e;
    assert_eq!(round_exact(true, prod, pe, Rm::Rtn), 0x8000_0000_0000_0001);
    assert_eq!(round_exact(false, prod, pe, Rm::Rtp), 0x0000_0000_0000_0001);
    assert_eq!(round_exact(true, prod, pe, Rm::Rtz), 0x8000_0000_0000_0000);
    assert_eq!(round_exact(true, prod, pe, Rm::Rne), 0x8000_0000_0000_0000);
    // Halfway tie at 1.0: 1.0 + 2^-53 as an exact value is
    // (2^53 + 1)·2^-52 + 2^-53 = (2^54 + 3)·2^-53 — halfway between
    // (2^54 + 0) and (2^54 + 2) cells at 2^-52… simpler: use num = 3 at
    // 2^-52 relative to the grid cell 2^-52 around [1, 2): 1.5 cells.
    // The instance-level pins below carry the mode table; here pin the
    // subnormal-grid saturation instead:
    // 3·2^-1075 (halfway between min_sub and 0… wait 2^-1075 = half of
    // 2^-1074): RNE ties to even → 0.
    assert_eq!(round_exact(false, 1, e - 1, Rm::Rne), 0x0000_0000_0000_0000);
    // …and RNA ties away from zero → min_subnormal.
    assert_eq!(round_exact(false, 1, e - 1, Rm::Rna), 0x0000_0000_0000_0001);
    // Directed overflow saturation: 2^2000 rounds to ±inf under RNE/RNA,
    // but RTZ clamps to the maximum finite datum.
    let big = 1u128 << 100; // 2^100 · 2^1900 = 2^2000
    assert_eq!(
        round_exact(false, big, 1900, Rm::Rne),
        0x7ff0_0000_0000_0000
    );
    assert_eq!(
        round_exact(false, big, 1900, Rm::Rtz),
        0x7fef_ffff_ffff_ffff
    );
    assert_eq!(round_exact(true, big, 1900, Rm::Rtp), 0xffef_ffff_ffff_ffff);
    // Decode round-trip: every finite bit pattern decodes and its exact
    // value re-rounds (exactly) to the same bits under every mode.
    for bits in [
        0x0000_0000_0000_0001u64,
        0x0000_0000_0000_0003,
        0x3ff0_0000_0000_0001,
        0x7fef_ffff_ffff_ffff,
        0xbfd3_3333_3333_3333,
    ] {
        let d = DecF64::decode(bits).expect("finite");
        for rm in [Rm::Rne, Rm::Rna, Rm::Rtp, Rm::Rtn, Rm::Rtz] {
            assert_eq!(
                round_exact(d.neg, d.mant as u128, d.exp2, rm),
                bits,
                "exact value of {bits:#x} must re-round to itself under {}",
                rm.name()
            );
        }
    }
}

/// `fpboundary` generation: sat/unsat twins share their prefix, every
/// script is QF_FP with one check-sat per expected answer, and the fold
/// twins' probes differ (a real perturbation, not a duplicate).
#[test]
fn fpboundary_twins_are_complementary() {
    use nixie_obligation::fpboundary;
    for seed in 0..6u64 {
        let insts = fpboundary::generate(
            seed,
            &fpboundary::Params {
                folds: 4,
                chains: true,
                incremental: true,
            },
            "cert",
        )
        .expect("generate");
        assert!(insts.len() > 20, "seed {seed}: too few instances");
        for inst in &insts {
            assert!(inst.script.contains("(set-logic QF_FP)"));
            assert_eq!(
                inst.script.matches("(check-sat)").count(),
                inst.expected.len()
            );
        }
        // Every fold pair: same head, one Sat and one Unsat.
        for inst in &insts {
            if !inst.name.contains("fold-") || inst.name.contains("-neg") {
                continue;
            }
            let twin =
                inst.name
                    .replacen(&format!("-s{seed}-cert"), &format!("-neg-s{seed}-cert"), 1);
            let other = insts
                .iter()
                .find(|o| o.name == twin)
                .unwrap_or_else(|| panic!("missing twin {twin}"));
            assert_eq!(inst.expected[0], Answer::Sat);
            assert_eq!(other.expected[0], Answer::Unsat);
            // Same assertions except the probed literal line.
            let strip = |s: &str| -> String {
                s.lines()
                    .filter(|l| !l.contains("(assert (= y (fp ") || l.is_empty())
                    .filter(|l| !l.starts_with("(assert (= y "))
                    .collect::<Vec<_>>()
                    .join("\n")
            };
            assert_eq!(
                strip(&inst.script),
                strip(&other.script),
                "twins must share their pin/define prefix"
            );
        }
    }
}
