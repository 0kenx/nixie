//! The seed-deduplication regression: the Gebauer–Möller discard is
//! UNSOUND when two basis elements share a leading monomial — the
//! duplicate trivially divides every lcm of its own multiples,
//! discarding pairs whose S-polynomials do not reduce to zero. Found
//! 2026-09-18 while validating the F4 engine against Buchberger on
//! random 5×6 product systems: a whole-ring ideal (an UNSAT goal with a
//! verified `1 = Σ cᵢ·fᵢ` witness) returned a 9-element non-basis with
//! `is_gb = true` — the refutation was silently missed.
//!
//! The fix reduces each INPUT's leading term against the other inputs
//! at initialization (leading-term dedup, NOT full inter-reduction —
//! the engine's "generators as given" rationale stands for everything
//! except lm-distinctness). These tests pin the fix: the exact
//! reproducer, and a randomized brute-force battery agreeing on
//! whole-ring detection and mutual ideal membership.

use nixie_math::ff::FieldCtx;
use nixie_math::ff::grobner::*;
use nixie_math::ff::poly::MPoly;
use nixie_math::polynomial::Monomial;
use num_bigint::BigUint;

/// Random product-of-affine-forms system (the shape that found the bug;
/// the F4 property tests share this generator family).
fn system(f: &FieldCtx, seed: u64, nvars: usize, ncons: usize) -> Vec<MPoly> {
    let c = |v: i64| f.from_bigint(&num_bigint::BigInt::from(v));
    let mut rng = seed;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };
    let mut inputs: Vec<MPoly> = Vec::new();
    for _ in 0..ncons {
        let mut pick = |r: usize| (next() as usize) % r;
        let idx = [pick(nvars), pick(nvars), pick(nvars), pick(nvars)];
        let co = [
            (next() % 37) as i64 + 1,
            (next() % 37) as i64 + 1,
            (next() % 37) as i64 + 1,
            (next() % 37) as i64 + 1,
        ];
        let mut lhs = MPoly::zero();
        for (which, coe) in [(idx[0], co[0]), (idx[1], co[1])] {
            let mut t = MPoly::zero();
            t.add_term(f, Monomial::from_var(which as u32), &c(coe));
            lhs = lhs.add(f, &t);
        }
        lhs.add_term(f, Monomial::unit(), &c((next() % 37) as i64));
        let mut rhs = MPoly::zero();
        for (which, coe) in [(idx[2], co[2]), (idx[3], co[3])] {
            let mut t = MPoly::zero();
            t.add_term(f, Monomial::from_var(which as u32), &c(coe));
            rhs = rhs.add(f, &t);
        }
        rhs.add_term(f, Monomial::unit(), &c((next() % 37) as i64));
        let mut prod = lhs.mul(f, &rhs);
        let mut planted = MPoly::zero();
        planted.add_term(f, Monomial::unit(), &c((next() % 97) as i64 + 1));
        prod = prod.sub(f, &planted);
        inputs.push(prod);
    }
    inputs
}

/// Brute-force Buchberger (every pair, no criteria) — the reference for
/// small systems. Returns whether the computed basis contains a nonzero
/// constant (the whole-ring witness).
fn brute_whole_ring(f: &FieldCtx, inputs: &[MPoly], steps: &mut usize) -> bool {
    let mut basis: Vec<MPoly> = inputs.iter().map(|p| p.monic(f, DEGREVLEX)).collect();
    basis.retain(|p| !p.is_zero());
    if basis.iter().any(|p| p.is_nonzero_constant()) {
        return true;
    }
    let nf_mod = |p: &MPoly, b: &[MPoly]| -> MPoly {
        let gb = GrobnerBasis {
            basis: b
                .iter()
                .map(|q| TracedPoly {
                    poly: q.clone(),
                    cofactors: Vec::new(),
                })
                .collect(),
            inputs: inputs.to_vec(),
        };
        normal_form(f, p, &gb, &mut GrobnerBudget::new(1 << 24)).unwrap_or(MPoly::zero())
    };
    let mut done: Vec<(usize, usize)> = Vec::new();
    loop {
        *steps += 1;
        if *steps > 20_000 {
            return false; // bounded probe; the small systems finish far earlier
        }
        let mut next: Option<(usize, usize)> = None;
        'outer: for i in 0..basis.len() {
            for j in (i + 1)..basis.len() {
                if !done.contains(&(i, j)) {
                    next = Some((i, j));
                    break 'outer;
                }
            }
        }
        let Some((i, j)) = next else { break };
        done.push((i, j));
        let (li, lj) = (
            basis[i].lm(DEGREVLEX).unwrap_or_else(Monomial::unit),
            basis[j].lm(DEGREVLEX).unwrap_or_else(Monomial::unit),
        );
        let lcm = nixie_math::ff::poly::monomial_lcm(&li, &lj);
        let qi = nixie_math::ff::poly::monomial_div(&lcm, &li).unwrap_or_else(Monomial::unit);
        let qj = nixie_math::ff::poly::monomial_div(&lcm, &lj).unwrap_or_else(Monomial::unit);
        let sp =
            mul_by_monomial_pub(f, &basis[i], &qi).sub(f, &mul_by_monomial_pub(f, &basis[j], &qj));
        let nf = nf_mod(&sp, &basis);
        if !nf.is_zero() {
            if nf.is_nonzero_constant() {
                return true;
            }
            basis.push(nf.monic(f, DEGREVLEX));
        }
    }
    false
}

/// The exact reproducer: seed 0xBEEF_0001 at 5×6 — a whole-ring ideal
/// whose constant witness (verified by exact cofactor re-multiplication
/// during the investigation) the engine returned a 9-element non-basis
/// for. The fix must find the refutation.
#[test]
fn whole_ring_witness_is_not_missed() {
    let f = FieldCtx::new(BigUint::from(2u64.pow(31) - 1)).unwrap();
    let inputs = system(&f, 0xBEEF_0001, 5, 6);
    let mut steps = 0;
    assert!(
        brute_whole_ring(&f, &inputs, &mut steps),
        "reproducer premise: the system's ideal is the whole ring"
    );
    let mut b = GrobnerBudget::new(1 << 24);
    let r = grobner_basis_untraced(&f, &inputs, &mut b).expect("completes");
    assert!(
        r.contains_nonzero_constant(),
        "the engine must detect the whole-ring ideal (missed refutation = wrong-verdict class)"
    );
}

/// Randomized battery: whole-ring agreement and mutual membership
/// between the engine and the brute reference, across many shapes
/// (including deliberately duplicate-lm seeds — two constraints over
/// the same variable pair).
#[test]
fn engine_agrees_with_brute_force() {
    let f = FieldCtx::new(BigUint::from(2u64.pow(31) - 1)).unwrap();
    for (seed, nvars, ncons) in [
        (0xF00D_CAFEu64, 3usize, 4usize),
        (0x0001, 3, 5),
        (0x0002, 4, 4),
        (0x0003, 4, 6),
        (0x0004, 5, 5),
        (0xBEEF_0001, 5, 6),
        (0x0005, 5, 7),
    ] {
        let inputs = system(&f, seed, nvars, ncons);
        let mut steps = 0;
        let brute_ring = brute_whole_ring(&f, &inputs, &mut steps);
        let mut b = GrobnerBudget::new(1 << 24);
        let r = grobner_basis_untraced(&f, &inputs, &mut b).expect("completes");
        let engine_ring = r.contains_nonzero_constant();
        assert_eq!(
            brute_ring, engine_ring,
            "whole-ring disagreement at seed {seed:#x} ({nvars}x{ncons}): brute={brute_ring} engine={engine_ring} (brute steps {steps})"
        );
        if engine_ring {
            continue; // {1}: mutual membership is trivial
        }
        // Mutual membership: every engine element is in the brute ideal
        // and vice versa (both complete, non-whole-ring).
        let mut b2 = GrobnerBudget::new(1 << 24);
        let brute_gb = {
            // Rebuild the brute basis (same loop, keeping elements).
            let mut basis: Vec<MPoly> = inputs.iter().map(|p| p.monic(&f, DEGREVLEX)).collect();
            basis.retain(|p| !p.is_zero());
            let nf_mod = |p: &MPoly, basis: &[MPoly]| -> MPoly {
                let gb = GrobnerBasis {
                    basis: basis
                        .iter()
                        .map(|q| TracedPoly {
                            poly: q.clone(),
                            cofactors: Vec::new(),
                        })
                        .collect(),
                    inputs: inputs.to_vec(),
                };
                normal_form(&f, p, &gb, &mut GrobnerBudget::new(1 << 24)).unwrap_or(MPoly::zero())
            };
            let mut done: Vec<(usize, usize)> = Vec::new();
            loop {
                let mut next: Option<(usize, usize)> = None;
                'outer: for i in 0..basis.len() {
                    for j in (i + 1)..basis.len() {
                        if !done.contains(&(i, j)) {
                            next = Some((i, j));
                            break 'outer;
                        }
                    }
                }
                let Some((i, j)) = next else { break };
                done.push((i, j));
                let (li, lj) = (
                    basis[i].lm(DEGREVLEX).unwrap_or_else(Monomial::unit),
                    basis[j].lm(DEGREVLEX).unwrap_or_else(Monomial::unit),
                );
                let lcm = nixie_math::ff::poly::monomial_lcm(&li, &lj);
                let qi =
                    nixie_math::ff::poly::monomial_div(&lcm, &li).unwrap_or_else(Monomial::unit);
                let qj =
                    nixie_math::ff::poly::monomial_div(&lcm, &lj).unwrap_or_else(Monomial::unit);
                let sp = mul_by_monomial_pub(&f, &basis[i], &qi)
                    .sub(&f, &mul_by_monomial_pub(&f, &basis[j], &qj));
                let nf = nf_mod(&sp, &basis);
                if !nf.is_zero() {
                    basis.push(nf.monic(&f, DEGREVLEX));
                }
            }
            let _ = &mut b2;
            GrobnerBasis {
                basis: basis
                    .iter()
                    .map(|q| TracedPoly {
                        poly: q.clone(),
                        cofactors: Vec::new(),
                    })
                    .collect(),
                inputs: inputs.to_vec(),
            }
        };
        for t in &r.basis {
            let nf = normal_form(&f, &t.poly, &brute_gb, &mut GrobnerBudget::new(1 << 24))
                .unwrap_or(MPoly::zero());
            assert!(
                nf.is_zero(),
                "engine element outside the brute ideal at seed {seed:#x}"
            );
        }
        let engine_gb = GrobnerBasis {
            basis: r.basis.clone(),
            inputs: inputs.to_vec(),
        };
        for t in &brute_gb.basis {
            let nf = normal_form(&f, &t.poly, &engine_gb, &mut GrobnerBudget::new(1 << 24))
                .unwrap_or(MPoly::zero());
            assert!(
                nf.is_zero(),
                "brute element outside the engine ideal at seed {seed:#x} (missed element)"
            );
        }
    }
}
