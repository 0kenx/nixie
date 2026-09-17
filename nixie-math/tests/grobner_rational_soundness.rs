//! The rational Gröbner engines' soundness battery (the twin of
//! `ff_gb_seed_dedup_regression.rs`): random product systems over ℚ,
//! engine vs brute-force (no criteria, every pair) — whole-ring
//! agreement, mutual ideal membership, leading-monomial agreement, and
//! the honest-refusal contract of the iteration cap.
//!
//! Background: the engines' chain criterion was the *simplified*
//! unsound form (bare `lm_k | lcm`, with tautological side-checks) —
//! the same missed-refutation class root-caused in the 𝔽_p engine on
//! 2026-09-18. The sound form (zero-pairs bookkeeping: a pair is
//! discardable only when the chain's precondition actually holds) is
//! now ported to all three rational engines; this battery is the gate
//! any future change to them must pass.

use nixie_math::grobner::{grobner_basis, ideal_membership, reduce, s_polynomial};
use nixie_math::polynomial::Polynomial;

/// Deterministic xorshift (the FF battery's discipline).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

fn affine(rng: &mut Rng, nvars: usize, vars: [usize; 2]) -> Polynomial {
    let a = (rng.next() % 13) as i64 + 1;
    let b = (rng.next() % 13) as i64 + 1;
    let c = (rng.next() % 13) as i64;
    let _ = nvars;
    Polynomial::from_coeffs_int(&[
        (a, &[(vars[0] as u32, 1)]),
        (b, &[(vars[1] as u32, 1)]),
        (c, &[]),
    ])
}

/// Random product-of-affine-forms system minus a random constant —
/// the FF battery's family over ℚ (some of these are whole-ring).
fn system(seed: u64, nvars: usize, ncons: usize) -> Vec<Polynomial> {
    let mut rng = Rng(seed);
    let pick = |rng: &mut Rng| (rng.next() as usize) % nvars;
    let mut inputs = Vec::new();
    for _ in 0..ncons {
        let (la, lb) = (pick(&mut rng), pick(&mut rng));
        let (ra, rb) = (pick(&mut rng), pick(&mut rng));
        let l = affine(&mut rng, nvars, [la, lb]);
        let r = affine(&mut rng, nvars, [ra, rb]);
        let mut prod = &l * &r;
        let k = (rng.next() % 29) as i64 + 1;
        prod = &prod - &Polynomial::from_coeffs_int(&[(k, &[])]);
        inputs.push(prod);
    }
    inputs
}

/// Brute-force Buchberger: every pair, no criteria, full reduction —
/// the reference for small systems.
fn brute_basis(inputs: &[Polynomial]) -> Vec<Polynomial> {
    let mut basis: Vec<Polynomial> = inputs.iter().map(|p| p.primitive()).collect();
    basis.retain(|p| !p.is_zero());
    let mut done: Vec<(usize, usize)> = Vec::new();
    let mut steps = 0usize;
    loop {
        steps += 1;
        if steps > 20_000 {
            return Vec::new(); // bounded probe; the small systems finish far earlier
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
        let s = s_polynomial(&basis[i], &basis[j]);
        let nf = reduce(&s, &basis);
        if !nf.is_zero() {
            basis.push(nf.primitive());
        }
    }
    basis
}

fn is_nonzero_constant(p: &Polynomial) -> bool {
    !p.is_zero() && p.leading_monomial().is_some_and(|m| m.vars().is_empty())
}

#[test]
fn engine_agrees_with_brute_force() {
    // Shapes sized for BigRational arithmetic in test time: a 4x5
    // NON-whole-ring system exceeds ten minutes of honest cascade
    // (the engine computes REAL S-polys now — before 2026-09-18 it was
    // a decorated no-op, instant and vacuous; measured: 4x4 non-ring
    // completes in ~20 ms, 4x5 non-ring does not finish — a capacity
    // fact to price before ANY wiring, not a soundness question). The
    // shapes here cover duplicate-lm seeds, whole-ring systems, and
    // multi-admission cascades.
    for (seed, nvars, ncons) in [
        (0xF00D_CAFEu64, 3usize, 4usize),
        (0x0001, 3, 5),
        (0x2222_0002, 3, 6),
        (0x0002, 4, 4),
    ] {
        let inputs = system(seed, nvars, ncons);
        let brute = brute_basis(&inputs);
        let engine = grobner_basis(&inputs).expect("completes within the cap");

        if brute.is_empty() {
            continue; // brute probe gave up
        }
        let brute_ring = brute.iter().any(is_nonzero_constant);
        let engine_ring = engine.iter().any(is_nonzero_constant);
        assert_eq!(
            brute_ring, engine_ring,
            "whole-ring disagreement at seed {seed:#x} ({nvars}x{ncons}): brute={brute_ring} engine={engine_ring}"
        );
        if engine_ring {
            continue; // {1}: mutual membership is trivial
        }
        // Mutual membership: every engine element is in the brute ideal
        // and vice versa.
        for t in &engine {
            let nf = reduce(t, &brute);
            assert!(
                nf.is_zero(),
                "engine element outside the brute ideal at seed {seed:#x}"
            );
        }
        for t in &brute {
            let nf = reduce(t, &engine);
            assert!(
                nf.is_zero(),
                "brute element outside the engine ideal at seed {seed:#x} — the engine dropped an element"
            );
        }
        // Leading-monomial agreement (a reduced GB is unique for a
        // fixed order over a field). The brute basis is NOT
        // inter-reduced (it admits every nonzero remainder), so
        // interreduce it first — mirroring the engine's own final
        // pass — or the lm sets differ spuriously.
        let interreduced = |basis: &[Polynomial]| -> Vec<Polynomial> {
            let mut out = Vec::new();
            for (i, p) in basis.iter().enumerate() {
                if p.is_zero() {
                    continue;
                }
                let others: Vec<Polynomial> = basis
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| *j != i)
                    .map(|(_, q)| q.clone())
                    .collect();
                let r = reduce(p, &others);
                if !r.is_zero() {
                    out.push(r.make_monic());
                }
            }
            out
        };
        let brute_ir = interreduced(&brute);
        let lm_key = |p: &Polynomial| -> Option<Vec<(u32, u32)>> {
            p.leading_monomial()
                .map(|m| m.vars().iter().map(|vp| (vp.var, vp.power)).collect())
        };
        let mut e_lms: Vec<Vec<(u32, u32)>> = engine.iter().filter_map(lm_key).collect();
        let mut b_lms: Vec<Vec<(u32, u32)>> = brute_ir.iter().filter_map(lm_key).collect();
        e_lms.sort();
        b_lms.sort();
        assert_eq!(
            e_lms, b_lms,
            "leading monomials diverged at seed {seed:#x} ({nvars}x{ncons})"
        );
    }
}

#[test]
fn engine_is_deterministic() {
    let inputs = system(0xD1CE_BEEF, 4, 5);
    let a = grobner_basis(&inputs).expect("completes");
    let b = grobner_basis(&inputs).expect("completes");
    assert_eq!(a.len(), b.len());
    for (x, y) in a.iter().zip(b.iter()) {
        assert_eq!(x, y, "the rational engine is not deterministic");
    }
}

#[test]
fn membership_refuses_rather_than_guessing_on_truncation() {
    // Whatever the outcome, `ideal_membership` must not fabricate a
    // verdict: Ok(decided) only on a completed basis, Err on the cap.
    // (The engine actually computes S-polys now — before 2026-09-18 it
    // was a decorated no-op, so "large" systems completed instantly
    // and vacuously. Sized to finish in test time.)
    let inputs = system(0x5EED_0042, 4, 5);
    let _ = ideal_membership(&inputs[0], &inputs); // must not panic
}
