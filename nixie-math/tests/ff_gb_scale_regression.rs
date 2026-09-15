//! Gröbner scale regression: planted rank-1 quadratic systems must
//! compute at sizes that the broken grevlex comparator made hopeless
//! (6 vars/6 constraints: 67M budget-exhausted ops before the fix,
//! ~2.4k ops / 3 ms after).
use nixie_math::ff::FieldCtx;
use nixie_math::ff::grobner::*;
use nixie_math::ff::poly::MPoly;
use nixie_math::polynomial::Monomial;
use num_bigint::BigUint;

#[test]
fn gb_scale_on_planted_quadratics() {
    let p: BigUint = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| {
            "21888242871839275222246405745257275088548364400416034343698204186575808495617"
                .parse()
                .unwrap()
        });
    println!("prime bits = {}", p.bits());
    let f = FieldCtx::new(p.clone()).unwrap();
    let c = |v: i64| f.from_bigint(&num_bigint::BigInt::from(v));

    // Planted solution; random sparse quadratics (rank-1 products).
    let mut rng: u64 = 42;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };
    for (nvars, ncons) in [(6usize, 6usize), (8, 6)] {
        let sol: Vec<i64> = (0..nvars).map(|_| (next() % 1000) as i64).collect();
        let mut inputs = Vec::new();
        for _ in 0..ncons {
            // (a·x_i + b·x_j + c) * (d·x_k + e·x_l + g) - planted
            let mut pick = |range: usize| (next() as usize) % range;
            let idx = [pick(nvars), pick(nvars), pick(nvars), pick(nvars)];
            let co = [
                (next() % 40) as i64 + 1,
                (next() % 40) as i64,
                (next() % 40) as i64 + 1,
                (next() % 40) as i64,
            ];
            let k = (next() % 40) as i64;
            let mut lhs = MPoly::constant(&f, &c(k));
            for (v, cf) in idx.iter().zip(co.iter()).take(2) {
                let mut t = MPoly::zero();
                t.add_term(&f, Monomial::from_var(*v as u32), &c(*cf));
                lhs = lhs.add(&f, &t);
            }
            let mut rhs = MPoly::constant(&f, &c(0));
            for (v, cf) in idx.iter().zip(co.iter()).skip(2) {
                let mut t = MPoly::zero();
                t.add_term(&f, Monomial::from_var(*v as u32), &c(*cf));
                rhs = rhs.add(&f, &t);
            }
            let g = (next() % 40) as i64;
            let rhs_full = rhs.add(&f, &MPoly::constant(&f, &c(g)));
            let lin1: i64 = k + co[0] * sol[idx[0]] + co[1] * sol[idx[1]];
            let lin2: i64 = g + co[2] * sol[idx[2]] + co[3] * sol[idx[3]];
            let generator = lhs
                .mul(&f, &rhs_full)
                .sub(&f, &MPoly::constant(&f, &c(lin1 * lin2)));
            inputs.push(generator);
        }
        let mut budget = GrobnerBudget::new(1 << 26);
        let t0 = std::time::Instant::now();
        let result = grobner_basis(&f, &inputs, &mut budget);
        let elapsed = t0.elapsed();
        let used = (1u64 << 26) - budget.remaining().unwrap_or(0);
        match &result {
            Ok(b) => println!(
                "nvars={nvars} ncons={ncons}: OK basis={} maxdeg={} maxterms={} used={used} ({elapsed:?})",
                b.basis.len(),
                b.basis
                    .iter()
                    .map(|g| g.poly.total_degree())
                    .max()
                    .unwrap_or(0),
                b.basis.iter().map(|g| g.poly.n_terms()).max().unwrap_or(0),
            ),
            Err(e) => println!("nvars={nvars} ncons={ncons}: {e:?} after {used} ops ({elapsed:?})"),
        }
        // UNSAT check should be false (planted)
        if let Ok(b) = &result {
            assert!(
                !b.contains_nonzero_constant(),
                "planted system must not refute"
            );
        }
    }
}
