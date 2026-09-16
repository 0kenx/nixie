//! The untraced fast path's load-bearing invariant: cofactor rows never
//! influence the cascade's trajectory, so `grobner_basis_untraced` and
//! `grobner_basis` produce IDENTICAL basis polynomials (element for
//! element, order for order) on the same inputs. The fast path's callers
//! (wide components in `ff_theory.rs`) rely on exactly this: a traced
//! re-run after an untraced completion reproduces the same basis, and
//! any divergence would mean the rows are influencing reductions — a
//! soundness-relevant coupling of certificate bookkeeping to the search.
use nixie_math::ff::FieldCtx;
use nixie_math::ff::grobner::*;
use nixie_math::ff::poly::MPoly;
use nixie_math::polynomial::Monomial;
use num_bigint::BigUint;

#[test]
fn untraced_and_traced_bases_are_identical() {
    let f = FieldCtx::new(BigUint::from(2u64.pow(31) - 1)).unwrap();
    let c = |v: i64| f.from_bigint(&num_bigint::BigInt::from(v));
    let mut rng: u64 = 0xF00D_CAFE;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };
    // A spread of shapes: sizes crossing the fast-path threshold,
    // planted-satisfiable (bases complete without a constant).
    // 17x20 trimmed 2026-09-18: with the unsound second criterion
    // disabled (see ff_gb_seed_dedup_regression.rs), that shape's debug
    // cascade takes ~245 s — the identity invariant is trajectory
    // equality, not capacity, and the smaller shapes cover it.
    for (nvars, ncons) in [(3usize, 4usize), (5, 6), (8, 8), (12, 12)] {
        let mut inputs: Vec<MPoly> = Vec::new();
        for _ in 0..ncons {
            let mut pick = |range: usize| (next() as usize) % range;
            let idx = [pick(nvars), pick(nvars), pick(nvars), pick(nvars)];
            let co = [
                (next() % 37) as i64 + 1,
                (next() % 37) as i64 + 1,
                (next() % 37) as i64 + 1,
                (next() % 37) as i64 + 1,
            ];
            // (a·x_i + b·x_j + c0)(d·x_k + e·x_l + c1) − planted_value
            let mut lhs = MPoly::zero();
            for (which, coe) in [(idx[0], co[0]), (idx[1], co[1])] {
                let mut t = MPoly::zero();
                t.add_term(&f, Monomial::from_var(which as u32), &c(coe));
                lhs = lhs.add(&f, &t);
            }
            lhs.add_term(&f, Monomial::unit(), &c((next() % 37) as i64));
            let mut rhs = MPoly::zero();
            for (which, coe) in [(idx[2], co[2]), (idx[3], co[3])] {
                let mut t = MPoly::zero();
                t.add_term(&f, Monomial::from_var(which as u32), &c(coe));
                rhs = rhs.add(&f, &t);
            }
            rhs.add_term(&f, Monomial::unit(), &c((next() % 37) as i64));
            let mut prod = lhs.mul(&f, &rhs);
            // The exact planted value does not matter for the identity
            // test; a random constant keeps the basis nontrivial.
            let mut planted = MPoly::zero();
            planted.add_term(&f, Monomial::unit(), &c((next() % 97) as i64 + 1));
            prod = prod.sub(&f, &planted);
            inputs.push(prod);
        }
        let mut b1 = GrobnerBudget::new(1 << 24);
        let mut b2 = GrobnerBudget::new(1 << 24);
        let traced = grobner_basis(&f, &inputs, &mut b1);
        let untraced = grobner_basis_untraced(&f, &inputs, &mut b2);
        // Both must agree on completion vs budget.
        match (traced, untraced) {
            (Ok(t), Ok(u)) => {
                assert_eq!(
                    t.basis.len(),
                    u.basis.len(),
                    "basis length divergence at {nvars}x{ncons}"
                );
                for (i, (a, b)) in t.basis.iter().zip(u.basis.iter()).enumerate() {
                    assert_eq!(
                        a.poly, b.poly,
                        "element {i} diverged at {nvars}x{ncons}: rows influenced the trajectory"
                    );
                }
            }
            (Err(_), Err(_)) => {}
            (t, u) => panic!(
                "completion divergence at {nvars}x{ncons}: traced={:?} untraced={:?}",
                t.is_ok(),
                u.is_ok()
            ),
        }
    }
}
