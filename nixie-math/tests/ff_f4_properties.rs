//! The F4 engine's correctness pins (`docs/studies/2026-09-18-ff-f4.md`):
//! F4 must compute a Gröbner basis of the SAME ideal as the Buchberger
//! engine on identical inputs. The strongest check is mutual ideal
//! membership (every F4 element reduces to 0 modulo the Buchberger basis
//! and vice versa — the property every downstream consumer relies on),
//! plus leading-monomial agreement on the reduced bases, determinism
//! across re-runs, constant detection on inconsistent systems, and
//! budget refusal.

use nixie_math::ff::FieldCtx;
use nixie_math::ff::grobner::*;
use nixie_math::ff::poly::MPoly;
use nixie_math::polynomial::Monomial;
use num_bigint::BigUint;

/// Random product-of-affine-forms system (the family whose validation
/// surfaced the engine's missed-refutation bug — see
/// ff_gb_seed_dedup_regression.rs; some of these systems are whole-ring).
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

#[test]
fn f4_and_buchberger_bases_agree() {
    let f = FieldCtx::new(BigUint::from(2u64.pow(31) - 1)).unwrap();
    for (seed, nvars, ncons) in [
        (0xF00D_CAFEu64, 3usize, 4usize),
        (0xBEEF_0001, 5, 6),
        (0xC0FF_EE00, 8, 8),
        (0x5EED_0042, 12, 12),
    ] {
        let inputs = system(&f, seed, nvars, ncons);
        // F4's measured ~8x cost: 2^28 covers it at these shapes so the
        // agreement is CHECKED rather than silently accepted by the
        // (Err, Err) arm (which hid 8x8's both-budget-out until the
        // sound chain criterion made Buchberger cheap enough to complete
        // there).
        let mut b1 = GrobnerBudget::new(1 << 24);
        let mut b2 = GrobnerBudget::new(1 << 28);
        let buch = grobner_basis_untraced(&f, &inputs, &mut b1);
        let f4r = f4_basis(&f, &inputs, &mut b2);
        match (buch, f4r) {
            (Ok(bb), Ok(fb)) => {
                assert_eq!(
                    bb.contains_nonzero_constant(),
                    fb.contains_nonzero_constant(),
                    "whole-ring disagreement at {nvars}x{ncons} (seed {seed:#x})"
                );
                if bb.contains_nonzero_constant() {
                    continue; // {1}: mutual membership is trivial
                }
                for t in &fb.basis {
                    let nf = normal_form(&f, &t.poly, &bb, &mut GrobnerBudget::new(1 << 24))
                        .unwrap_or(MPoly::zero());
                    assert!(
                        nf.is_zero(),
                        "F4 element not in the Buchberger ideal ({nvars}x{ncons})"
                    );
                }
                for t in &bb.basis {
                    let nf = normal_form(&f, &t.poly, &fb, &mut GrobnerBudget::new(1 << 24))
                        .unwrap_or(MPoly::zero());
                    assert!(
                        nf.is_zero(),
                        "Buchberger element not in the F4 ideal ({nvars}x{ncons}) — F4 dropped an element"
                    );
                }
                let mut bb_lms: Vec<String> = bb
                    .basis
                    .iter()
                    .map(|t| format!("{:?}", t.poly.lm(DEGREVLEX)))
                    .collect();
                let mut fb_lms: Vec<String> = fb
                    .basis
                    .iter()
                    .map(|t| format!("{:?}", t.poly.lm(DEGREVLEX)))
                    .collect();
                bb_lms.sort();
                fb_lms.sort();
                assert_eq!(
                    bb_lms, fb_lms,
                    "leading monomials diverged ({nvars}x{ncons})"
                );
            }
            (Err(_), Err(_)) => {}
            (a, b) => panic!("completion disagreement at {nvars}x{ncons}: buch={a:?} f4={b:?}"),
        }
    }
}

#[test]
fn f4_is_deterministic() {
    let f = FieldCtx::new(BigUint::from(2u64.pow(31) - 1)).unwrap();
    let inputs = system(&f, 0xD1CE_BEEF, 9, 10);
    // Measured (2026-09-18): this 9x10 shape costs F4 ~2^27 monomial
    // ops — about 8x Buchberger's. The prototype is CORRECT (see the
    // agreement test) but unoptimized (row construction clones, O(basis)
    // reducer scans per monomial); it is not wired into any solver path.
    // Optimization is the study's named follow-up.
    let mut b1 = GrobnerBudget::new(1 << 28);
    let mut b2 = GrobnerBudget::new(1 << 28);
    let r1 = f4_basis(&f, &inputs, &mut b1).expect("completes");
    let r2 = f4_basis(&f, &inputs, &mut b2).expect("completes");
    assert_eq!(r1.basis.len(), r2.basis.len());
    for (a, b) in r1.basis.iter().zip(r2.basis.iter()) {
        assert_eq!(a.poly, b.poly, "F4 is not deterministic");
    }
}

#[test]
fn f4_detects_the_whole_ring() {
    let f = FieldCtx::new(BigUint::from(97u64)).unwrap();
    // x·(x−1) and x are inconsistent: the basis contains a constant.
    let mut x2 = MPoly::zero();
    x2.add_term(
        &f,
        {
            let m = Monomial::from_var(0);
            m.mul(&Monomial::from_var(0))
        },
        &f.one(),
    );
    let mut one = MPoly::zero();
    one.add_term(&f, Monomial::unit(), &f.one());
    let g1 = x2.sub(&f, &one);
    let mut g2 = MPoly::zero();
    g2.add_term(&f, Monomial::from_var(0), &f.one());
    let mut b = GrobnerBudget::new(1 << 24);
    let r = f4_basis(&f, &[g1, g2], &mut b).expect("completes");
    assert!(
        r.contains_nonzero_constant(),
        "an inconsistent system must yield a constant in the F4 basis"
    );
}

#[test]
fn f4_refuses_on_budget() {
    let f = FieldCtx::new(BigUint::from(2u64.pow(31) - 1)).unwrap();
    let inputs = system(&f, 0x5EED_0042, 12, 12);
    let mut b = GrobnerBudget::new(16);
    assert!(
        f4_basis(&f, &inputs, &mut b).is_err(),
        "a starved F4 must refuse, never fabricate"
    );
}
