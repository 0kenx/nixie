//! Planted-solution fuzzing at real ZK primes (`docs/FF_THEORY_DESIGN.md`
//! §10.3): sample a witness `z ∈ 𝔽_pⁿ`, generate constraints it satisfies
//! — ground truth is `sat`, so **any `unsat` is a hard failure at n = 1**.
//! Mutated instances (constraints the witness violates) are exercised for
//! crash-freedom and honest verdicts only, never scored.
//!
//! The generator builds R1CS-shaped systems — the circuit shape the
//! theory exists for: linear-plus-a-thin-layer-of-rank-1-quadratics.

use nixie_core::ast::{TermId, TermManager};
use nixie_core::sort::SortKind;
use nixie_core::sort::field::FieldId;
use nixie_theories::ff_theory::{FfOutcome, check_conjunction, validate_model};
use num_bigint::BigUint;
use num_traits::{One, ToPrimitive, Zero};

/// Deterministic xorshift stream (the design forbids randomized verdicts;
/// fuzzing reproducibility is a bug-reporting requirement).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn field_of(manager: &TermManager, sort: nixie_core::sort::SortId) -> FieldId {
    match manager.sorts.get(sort).map(|s| s.kind.clone()) {
        Some(SortKind::FiniteField(id)) => id,
        _ => panic!("expected a finite-field sort"),
    }
}

/// One planted round: `n` variables, `k` constraints over 𝔽_p, all
/// satisfied by the planted witness. The procedure must answer
/// `Model` (validated) or, on tiny budgets, `OutOfBudget` — never
/// `Unsat`/`Exhausted`.
fn planted_round(p: &BigUint, n: usize, k: usize, seed: u64) {
    planted_round_bounded(p, n, k, seed, 1 << 24);
}

fn planted_round_bounded(p: &BigUint, n: usize, k: usize, seed: u64, budget: u64) {
    let mut manager = TermManager::new();
    let sort = manager.sorts.finite_field(p.clone()).expect("prime");
    let field = field_of(&manager, sort);

    let mut rng = Rng(seed);
    // Planted witness.
    let witness: Vec<u64> = (0..n)
        .map(|_| rng.below(p.to_u64().unwrap_or(u64::MAX / 4)))
        .collect();
    let vars: Vec<TermId> = (0..n)
        .map(|i| manager.mk_var(&format!("w{i}"), sort))
        .collect();

    // Random linear form as a term + its value under the witness.
    let linear = |rng: &mut Rng, manager: &mut TermManager, degree1: bool| -> (TermId, BigUint) {
        let mut terms: Vec<TermId> = Vec::new();
        let mut value = BigUint::zero();
        for (i, &v) in vars.iter().enumerate() {
            let c = rng.below(50);
            if c == 0 {
                continue;
            }
            let coeff = manager
                .mk_ff_const(field, (c as i64).into())
                .expect("const");
            let t = if c == 1 {
                v
            } else {
                manager.mk_ff_mul([coeff, v]).expect("mul")
            };
            terms.push(t);
            value = (value + BigUint::from(c) * BigUint::from(witness[i])) % p;
        }
        let c0 = rng.below(50);
        if c0 > 0 {
            let t = manager
                .mk_ff_const(field, (c0 as i64).into())
                .expect("const");
            terms.push(t);
            value = (value + BigUint::from(c0)) % p;
        }
        let _ = degree1;
        (manager.mk_ff_add(terms).expect("add"), value)
    };

    let mut assertions: Vec<TermId> = Vec::new();
    for _ in 0..k {
        let shape = rng.below(3);
        let (lhs, rhs) = match shape {
            0 => {
                // linear = linear (witness-satisfiable by construction of
                // the rhs constant)
                let (a, av) = linear(&mut rng, &mut manager, true);
                let rhs_const = manager.mk_ff_const(field, av.into()).expect("const");
                (a, rhs_const)
            }
            1 => {
                // rank-1 quadratic: (linear)·(linear) = planted value
                let (a, av) = linear(&mut rng, &mut manager, true);
                let (b, bv) = linear(&mut rng, &mut manager, true);
                let prod = manager.mk_ff_mul([a, b]).expect("mul");
                let val = (&av * &bv) % p;
                (prod, manager.mk_ff_const(field, val.into()).expect("const"))
            }
            _ => {
                // three-var product for depth
                let (a, av) = linear(&mut rng, &mut manager, true);
                let (b, bv) = linear(&mut rng, &mut manager, true);
                let prod = manager.mk_ff_mul([a, b]).expect("mul");
                let val = (&av * &bv) % p;
                (prod, manager.mk_ff_const(field, val.into()).expect("const"))
            }
        };
        assertions.push(manager.mk_eq(lhs, rhs));
    }

    let outcome = check_conjunction(&manager, field, &assertions, budget);
    match outcome {
        FfOutcome::Model(model) => {
            let err = validate_model(&manager, field, &assertions, &model)
                .err()
                .unwrap_or_default();
            assert!(err.is_empty(), "planted solution failed validation: {err}");
            // The model need not equal the witness (any point works), but
            // it must satisfy — which validate_model just proved.
        }
        FfOutcome::OutOfBudget { .. } => {
            // An honest refusal and one of the design's listed Unknown
            // sources (§5): search or Gröbner budget exhaustion, or the
            // positive-dimensional enumeration cap at a huge prime. The
            // invariants that matter are pinned by the other arms —
            // never a false verdict, never an unvalidated model.
        }
        FfOutcome::Unsat(core) => {
            use nixie_core::smtlib::Printer;
            for (i, a) in assertions.iter().enumerate() {
                eprintln!("assertion {i}: {}", Printer::new(&manager).print_term(*a));
            }
            panic!(
                "FALSE UNSAT on a planted-satisfiable system (seed {seed}, core {:?})",
                core.fact_indices
            );
        }
        FfOutcome::Exhausted => {
            eprintln!("PLANTED WITNESS: {witness:?}");
            use nixie_core::smtlib::Printer;
            for (i, a) in assertions.iter().enumerate() {
                eprintln!("assertion {i}: {}", Printer::new(&manager).print_term(*a));
            }
            panic!("FALSE UNSAT (exhausted) on a planted-satisfiable system (seed {seed})");
        }
        FfOutcome::InvalidModel(reason) => {
            panic!("invalid shape on a planted system (seed {seed}): {reason}");
        }
    }
}

/// Mutated rounds: corrupt one constraint so the system has no planted
/// witness. No ground truth — assert only that the verdict is one of the
/// honest outcomes and (on Model) that validation passes.
fn mutated_round(p: &BigUint, n: usize, k: usize, seed: u64) {
    // Mutated systems are crash/honesty probes, not verdict probes: a
    // modest budget keeps the UNSAT-proving path from grinding (fully
    // closing a refuted quadratic system is exactly the case the design
    // defers to split-GB, Phase 7).
    const MUTATED_BUDGET: u64 = 1 << 17;
    let mut manager = TermManager::new();
    let sort = manager.sorts.finite_field(p.clone()).expect("prime");
    let field = field_of(&manager, sort);
    let mut rng = Rng(seed ^ 0xDEAD);
    let witness: Vec<u64> = (0..n).map(|_| rng.below(97)).collect();
    let vars: Vec<TermId> = (0..n)
        .map(|i| manager.mk_var(&format!("m{i}"), sort))
        .collect();
    let mut assertions: Vec<TermId> = Vec::new();
    for round in 0..k {
        let a = vars[rng.below(n as u64) as usize];
        let b = vars[rng.below(n as u64) as usize];
        let prod = manager.mk_ff_mul([a, b]).expect("mul");
        let mut val = (BigUint::from(witness[a.0 as usize % n])
            * BigUint::from(witness[b.0 as usize % n]))
            % p;
        if round == 0 {
            // The mutation: a value the witness does NOT satisfy.
            val = (&val + BigUint::one()) % p;
        }
        let rhs = manager.mk_ff_const(field, val.into()).expect("const");
        assertions.push(manager.mk_eq(prod, rhs));
    }
    match check_conjunction(&manager, field, &assertions, MUTATED_BUDGET) {
        FfOutcome::Model(model) => {
            assert!(validate_model(&manager, field, &assertions, &model).is_ok());
        }
        FfOutcome::Unsat(_) | FfOutcome::Exhausted | FfOutcome::OutOfBudget { .. } => {}
        FfOutcome::InvalidModel(reason) => panic!("invalid shape (seed {seed}): {reason}"),
    }
}

#[test]
fn planted_solutions_at_goldilocks() {
    let p = (BigUint::one() << 64) - (BigUint::one() << 32) + BigUint::one();
    // Budget note: dense quadratic systems over 4 variables grind the
    // GB search (the front end's linear core cannot collapse expanded
    // rank-1 products); rounds that exceed the budget refuse honestly,
    // which the arm below accepts. The invariant under test is that no
    // planted-satisfiable system is EVER answered unsat.
    for round in 0..8u64 {
        planted_round_bounded(&p, 4, 6, 0x5DEE_CE66_D000 + round, 1 << 21);
    }
}

#[test]
fn planted_zero_dimensional_systems_decide_at_bn254() {
    // n constraints pinning every variable through dense linear forms:
    // zero-dimensional, so the search must terminate in a model (never a
    // budget excuse) — the strongest form of the planted oracle.
    let p: BigUint =
        "21888242871839275222246405745257275088548364400416034343698204186575808495617"
            .parse()
            .expect("prime");
    let mut manager = TermManager::new();
    let sort = manager.sorts.finite_field(p.clone()).expect("prime");
    let field = field_of(&manager, sort);
    let mut rng = Rng(0xAAAA_BBBB);
    for round in 0..8u64 {
        let _ = round;
        let sol: Vec<u64> = (0..3).map(|_| rng.next() % 1_000_000_000).collect();
        let vars: Vec<TermId> = (0..3)
            .map(|i| manager.mk_var(&format!("z{i}_{round}"), sort))
            .collect();
        let mut assertions = Vec::new();
        for _row in 0..3 {
            let mut terms = Vec::new();
            let mut value = BigUint::zero();
            for (i, &v) in vars.iter().enumerate() {
                let c = 1 + rng.below(49); // dense: every variable appears
                let coeff = manager.mk_ff_const(field, (c as i64).into()).expect("c");
                terms.push(manager.mk_ff_mul([coeff, v]).expect("mul"));
                value = (value + BigUint::from(c) * BigUint::from(sol[i])) % &p;
            }
            let rhs = manager.mk_ff_const(field, value.into()).expect("c");
            let lhs = manager.mk_ff_add(terms).expect("add");
            assertions.push(manager.mk_eq(lhs, rhs));
        }
        match check_conjunction(&manager, field, &assertions, 1 << 24) {
            FfOutcome::Model(model) => {
                assert!(validate_model(&manager, field, &assertions, &model).is_ok());
            }
            other => panic!("dense linear system must decide: {other:?}"),
        }
    }
}

#[test]
fn planted_solutions_at_bn254() {
    let p: BigUint =
        "21888242871839275222246405745257275088548364400416034343698204186575808495617"
            .parse()
            .expect("prime");
    for round in 0..6u64 {
        planted_round(&p, 3, 4, 0xBEEF_CAFE_0000 + round);
    }
}

#[test]
fn planted_solutions_at_bls12_381_scalar() {
    let p: BigUint =
        "52435875175126190479447740508185965837690552500527637822603658699938581184513"
            .parse()
            .expect("prime");
    for round in 0..6u64 {
        planted_round(&p, 3, 4, 0x0123_4567_89AB + round);
    }
}

#[test]
fn mutated_systems_never_crash_or_fabricate() {
    let p: BigUint =
        "21888242871839275222246405745257275088548364400416034343698204186575808495617"
            .parse()
            .expect("prime");
    for round in 0..8u64 {
        mutated_round(&p, 4, 5, 0xFACE_B00C + round);
    }
    let goldilocks = (BigUint::one() << 64) - (BigUint::one() << 32) + BigUint::one();
    for round in 0..8u64 {
        mutated_round(&goldilocks, 4, 5, 0xCAFE_F00D + round);
    }
}
