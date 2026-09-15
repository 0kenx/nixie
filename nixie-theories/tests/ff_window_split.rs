//! The §6.5 window-decomposition regressions: locality-structured
//! planted systems whose monolithic cascade and 2-way split budget out,
//! so the verdict can only come from the variable-subset windows +
//! exchange + union cascade. Ground truth is the planted witness
//! (`docs/FF_THEORY_DESIGN.md` §10.3): any `unsat` on a planted system
//! is a hard failure; the model must validate exactly.
//!
//! The systems mirror the `bench/ff` chain corpus's shape — linear rows
//! over disjoint triples plus quadratic products over sliding pairs —
//! at a size small enough for a unit test but coupled enough that the
//! monolithic cascade is the expensive path.

use nixie_core::ast::{TermId, TermManager};
use nixie_core::sort::SortKind;
use nixie_core::sort::field::FieldId;
use nixie_theories::ff_theory::{FfOutcome, check_conjunction, validate_model};
use num_bigint::BigUint;
use num_traits::One;

/// Deterministic xorshift (the oracle files' discipline).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    /// A coefficient in [1, p).
    fn coeff(&mut self, p: &BigUint) -> BigUint {
        let m = p - BigUint::one();
        (BigUint::from(self.next() % 9973u64) + BigUint::one()) % m.clone()
    }
}

/// A planted locality chain over 𝔽_p: `n_vars` variables (multiple of
/// 3), a linear row per disjoint triple, a quadratic product per
/// sliding pair. Every constraint's RHS is its LHS evaluated at the
/// planted witness, so the system is satisfiable by construction;
/// `corrupt` shifts one RHS by 1 (index into rows-then-quads).
fn planted_chain(
    manager: &mut TermManager,
    p: &BigUint,
    n_vars: usize,
    corrupt: Option<usize>,
) -> (FieldId, Vec<TermId>) {
    assert!(n_vars.is_multiple_of(3), "triples need a multiple of 3");
    let sort = manager.sorts.finite_field(p.clone()).expect("prime");
    let field = match manager.sorts.get(sort).map(|s| s.kind.clone()) {
        Some(SortKind::FiniteField(id)) => id,
        other => panic!("expected a finite-field sort, got {other:?}"),
    };
    let mut rng = Rng(0x5eed_1234_abcd_0000u64.wrapping_add(n_vars as u64));
    let witness: Vec<BigUint> = (0..n_vars)
        .map(|i| {
            let m = p - BigUint::one();
            BigUint::from((rng.next() % 9973) + 17 + i as u64) % m.clone()
        })
        .collect();
    let vars: Vec<TermId> = (0..n_vars)
        .map(|i| manager.mk_var(&format!("w{i}"), sort))
        .collect();
    let const_of = |manager: &mut TermManager, v: &BigUint| {
        let i = num_bigint::BigInt::from(v.clone());
        manager.mk_ff_const(field, i).expect("field constant")
    };
    let mut assertions: Vec<TermId> = Vec::new();
    let n_rows = n_vars / 3;
    for r in 0..n_rows {
        let (i, j, k) = (3 * r, 3 * r + 1, 3 * r + 2);
        let (a, b, c, d) = (rng.coeff(p), rng.coeff(p), rng.coeff(p), rng.coeff(p));
        let mut rhs = (&a * &witness[i] + &b * &witness[j] + &c * &witness[k] + &d) % p;
        if corrupt == Some(r) {
            rhs = (rhs + BigUint::one()) % p;
        }
        let (ca, cb, cc, cd) = (
            const_of(manager, &a),
            const_of(manager, &b),
            const_of(manager, &c),
            const_of(manager, &d),
        );
        let ai = manager.mk_ff_mul([vars[i], ca]).expect("mul");
        let bj = manager.mk_ff_mul([vars[j], cb]).expect("mul");
        let ck = manager.mk_ff_mul([vars[k], cc]).expect("mul");
        let lhs = manager.mk_ff_add([ai, bj, ck, cd]).expect("add");
        let r = const_of(manager, &rhs);
        assertions.push(manager.mk_eq(lhs, r));
    }
    let n_quads = n_vars - 2;
    for q in 0..n_quads {
        let (i, j) = (q, q + 2);
        let (a, b, c, e) = (rng.coeff(p), rng.coeff(p), rng.coeff(p), rng.coeff(p));
        let mut rhs = ((&a * &witness[i] + &b) % p * ((&c * &witness[j] + &e) % p)) % p;
        if corrupt == Some(n_rows + q) {
            rhs = (rhs + BigUint::one()) % p;
        }
        let (ca, cb, cc, ce) = (
            const_of(manager, &a),
            const_of(manager, &b),
            const_of(manager, &c),
            const_of(manager, &e),
        );
        let left = {
            let m = manager.mk_ff_mul([vars[i], ca]).expect("mul");
            manager.mk_ff_add([m, cb]).expect("add")
        };
        let right = {
            let m = manager.mk_ff_mul([vars[j], cc]).expect("mul");
            manager.mk_ff_add([m, ce]).expect("add")
        };
        let lhs = manager.mk_ff_mul([left, right]).expect("mul");
        let r = const_of(manager, &rhs);
        assertions.push(manager.mk_eq(lhs, r));
    }
    (field, assertions)
}

/// A prime beyond the round-robin horizon: the verdict cannot come from
/// enumeration, only from the windows' pins.
const P: u32 = 65537;

#[test]
fn planted_local_chain_solves_and_validates() {
    let p = BigUint::from(P);
    let mut manager = TermManager::new();
    let (field, assertions) = planted_chain(&mut manager, &p, 15, None);
    // The default-scale budget: the planted chain must solve and its
    // model must validate exactly. (Routing through the windows cannot
    // be forced at this scale — the monolithic cascade is the cheapest
    // strategy for small goals; the window path's routing and capacity
    // pin is the bench/ff chain corpus, exercised end-to-end by the
    // release binary in the study.)
    let outcome = check_conjunction(&manager, field, &assertions, 1 << 24);
    match outcome {
        FfOutcome::Model(model) => {
            assert!(
                !model.assignments().is_empty(),
                "model must assign variables"
            );
            assert!(
                validate_model(&manager, field, &assertions, &model).is_ok(),
                "planted-chain model must validate exactly"
            );
        }
        other => panic!("planted-satisfiable locality chain must be sat, got {other:?}"),
    }
    // Determinism: the same input must produce the same flavour.
    let again = check_conjunction(&manager, field, &assertions, 1 << 24);
    assert!(matches!(again, FfOutcome::Model(_)));
}

#[test]
fn corrupted_local_chain_never_answers_sat() {
    let p = BigUint::from(P);
    let mut manager = TermManager::new();
    // Corrupt one quadratic's RHS: the corruption may or may not be
    // exposed within the stress budget, but a `sat` is impossible —
    // the model validation gate would have to fail first, and that
    // path is an Unknown, never a verdict.
    let (field, assertions) = planted_chain(&mut manager, &p, 15, Some(5 + 8));
    let outcome = check_conjunction(&manager, field, &assertions, 1 << 16);
    match outcome {
        FfOutcome::Unsat(core) => {
            assert!(
                !core.fact_indices.is_empty(),
                "an unsat core must name asserted literals"
            );
        }
        FfOutcome::OutOfBudget { .. } | FfOutcome::InvalidModel(_) => {}
        other => panic!("corrupted chain must not be sat, got {other:?}"),
    }
}

#[test]
fn skipped_window_refuses_never_guesses() {
    let p = BigUint::from(P);
    let mut manager = TermManager::new();
    let (field, assertions) = planted_chain(&mut manager, &p, 15, None);
    // A budget so small that windows themselves budget out: the outcome
    // must be OutOfBudget (Unknown at the solver layer), never a
    // verdict — the fast-refuse gate for skipped windows at p > 256.
    let outcome = check_conjunction(&manager, field, &assertions, 1 << 8);
    match outcome {
        FfOutcome::OutOfBudget { .. } | FfOutcome::InvalidModel(_) => {}
        other => panic!("a starved window split must refuse, got {other:?}"),
    }
}
