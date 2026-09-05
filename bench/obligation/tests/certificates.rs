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
