//! The §6.5 window-decomposition regressions: locality-structured
//! planted systems whose verdict can only come from the variable-subset
//! windows + worklist exchange + union cascade. Ground truth is the
//! planted witness (`docs/FF_THEORY_DESIGN.md` §10.3): any `unsat` on a
//! planted system is a hard failure; the model must validate exactly.
//!
//! ROUTING, the part small tests could never pin before: the systems
//! here are sized (see `ROUTING_BUDGET`'s probe note) so that the
//! monolithic cascade AND the 2-way split budget out first — a `Model`
//! verdict at that budget can only have come through the window path.
//! If the window path regresses, these tests degrade to `OutOfBudget`
//! and fail; no instrumentation needed.

use nixie_core::ast::{TermId, TermManager};
use nixie_core::sort::SortKind;
use nixie_core::sort::field::FieldId;
use nixie_theories::ff_theory::{FfOutcome, check_conjunction, validate_model};
use num_bigint::BigUint;
use num_traits::{One, Zero};

/// Deterministic xorshift (the oracle files' discipline).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    /// A coefficient in [1, p), mirroring the corpus generator's range.
    fn coeff(&mut self, p: &BigUint) -> BigUint {
        let m = p - BigUint::one();
        (BigUint::from(self.next() % 9973u64) + BigUint::one()) % m.clone()
    }
}

/// A planted locality chain over 𝔽_p in the CORPUS family's shape
/// (`bench/ff/gen_chain.py` — the residue-pass structure is
/// load-bearing): rows and quads come in passes at base offsets
/// 6k with row offset r ∈ {0,1,2} and quad offset pairs
/// (2,4), (3,5), (4,6), plus the closing row {3,4,5} and seam quads
/// {1,2,3},{5,6,7},{7,8,9} — ~1.5 constraints per variable. A naive
/// stride-6 ring (this file's first generator) chains the RREF
/// eliminations globally and nothing window-shaped survives (measured
/// in the 2026-09-17 study addendum).
///
/// Every RHS is the LHS evaluated at the planted witness, so the system
/// is satisfiable by construction; `corrupt` shifts one constraint's
/// RHS by 1 (index into the emission order).
fn planted_chain(
    manager: &mut TermManager,
    p: &BigUint,
    n_vars: usize,
    corrupt: Option<usize>,
) -> (FieldId, Vec<TermId>) {
    assert!(n_vars.is_multiple_of(4), "passes need a multiple of 4");
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

    // An affine form over the given variables: (term, value at witness).
    let affine = |rng: &mut Rng, manager: &mut TermManager, idxs: &[usize]| -> (TermId, BigUint) {
        let mut value = BigUint::zero();
        let mut ops = Vec::with_capacity(idxs.len() + 1);
        for &i in idxs {
            let c = rng.coeff(p);
            value = (&value + &c * &witness[i]) % p;
            let cc = const_of(manager, field, &c);
            ops.push(manager.mk_ff_mul([vars[i], cc]).expect("mul"));
        }
        let k = rng.coeff(p);
        value = (&value + &k) % p;
        ops.push(const_of(manager, field, &k));
        (manager.mk_ff_add(ops).expect("add"), value)
    };

    let mut assertions: Vec<TermId> = Vec::new();
    let mut emitted = 0usize;
    let mut assert_eq = |manager: &mut TermManager, lhs: TermId, value: BigUint| {
        let mut rhs = value;
        if corrupt == Some(emitted) {
            rhs = (rhs + BigUint::one()) % p;
        }
        let r = const_of(manager, field, &rhs);
        assertions.push(manager.mk_eq(lhs, r));
        emitted += 1;
    };

    let max_rows = n_vars / 2;
    let max_quads = n_vars;
    let mut rows = 0usize;
    let mut quads = 0usize;

    for (r_off, q1, q2) in [(0usize, 2usize, 4usize), (1, 3, 5), (2, 4, 6)] {
        let mut k = 0usize;
        loop {
            let base = 6 * k;
            let mut did = false;
            if base + r_off + 2 < n_vars && rows < max_rows {
                let (lhs, v) = affine(
                    &mut rng,
                    manager,
                    &[base + r_off, base + r_off + 1, base + r_off + 2],
                );
                assert_eq(manager, lhs, v);
                rows += 1;
                did = true;
            }
            for q_off in [q1, q2] {
                if base + q_off + 2 < n_vars && quads < max_quads {
                    let mid = base + q_off + 1;
                    let (l, lv) = affine(&mut rng, manager, &[base + q_off, mid]);
                    let (r, rv) = affine(&mut rng, manager, &[mid, base + q_off + 2]);
                    let lhs = manager.mk_ff_mul([l, r]).expect("mul");
                    assert_eq(manager, lhs, (lv * rv) % p);
                    quads += 1;
                    did = true;
                }
            }
            if !did {
                break;
            }
            k += 1;
        }
        if rows >= max_rows && quads >= max_quads {
            break;
        }
    }
    // The closing row and the seam quads (the cycle's closure).
    if rows < max_rows {
        let (lhs, v) = affine(&mut rng, manager, &[3, 4, 5]);
        assert_eq(manager, lhs, v);
        rows += 1;
    }
    for start in [1usize, 5, 7] {
        if quads < max_quads && start + 2 < n_vars {
            let (l, lv) = affine(&mut rng, manager, &[start, start + 1]);
            let (r, rv) = affine(&mut rng, manager, &[start + 1, start + 2]);
            let lhs = manager.mk_ff_mul([l, r]).expect("mul");
            assert_eq(manager, lhs, (lv * rv) % p);
            quads += 1;
        }
    }
    assert_eq!(rows, max_rows, "exact corpus density: n/2 affine rows");
    assert!(quads + 3 >= max_quads, "near-exact quad density (n quads)");

    (field, assertions)
}

fn const_of(manager: &mut TermManager, field: FieldId, v: &BigUint) -> TermId {
    let i = num_bigint::BigInt::from(v.clone());
    manager.mk_ff_const(field, i).expect("field constant")
}

/// A prime beyond the round-robin horizon: the verdict cannot come from
/// enumeration, only from the windows' pins.
const P: u32 = 65537;

/// The budget at which a `Model` verdict on `planted_chain(48)` can
/// ONLY come through the window path. Verified with NIXIE_FF_STATS at
/// this budget: the monolithic cascade over the 71-generator component
/// budget-outs, the 2-way split's nl-GB budget-outs, and the verdict
/// arrives via 8 eight-variable windows + the worklist exchange + the
/// union cascade (a `split-merged` basis). This turns the routing
/// property — previously only measurable on the release corpus — into a
/// per-run test invariant: a window-path regression degrades the
/// outcome to `OutOfBudget` and fails here. (Recalibrated 2^16 → 2^18
/// when the unsound GM second criterion was disabled — the window GBs
/// process more pairs now; the monolithic and split nl-GB still
/// budget-out far below any budget that completes the windows.)
const ROUTING_BUDGET: u64 = 1 << 18;

#[test]
fn window_path_routes_solves_and_validates() {
    let p = BigUint::from(P);
    let mut manager = TermManager::new();
    let (field, assertions) = planted_chain(&mut manager, &p, 48, None);
    let outcome = check_conjunction(&manager, field, &assertions, ROUTING_BUDGET);
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
        other => panic!(
            "the planted chain must solve through the window path at the \
             routing budget, got {other:?}"
        ),
    }
    // Determinism: identical flavour on a re-run.
    let again = check_conjunction(&manager, field, &assertions, ROUTING_BUDGET);
    assert!(matches!(again, FfOutcome::Model(_)));
}

#[test]
fn corrupted_chain_never_answers_sat() {
    let p = BigUint::from(P);
    let mut manager = TermManager::new();
    // Corrupt one quad's RHS (emission index 30 lands inside the second
    // pass): the chain may or may not expose the corruption within the
    // routing budget, but `sat` is impossible — the model-validation
    // gate would have to fail first, and that path answers Unknown.
    let (field, assertions) = planted_chain(&mut manager, &p, 48, Some(30));
    let outcome = check_conjunction(&manager, field, &assertions, ROUTING_BUDGET);
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
fn starved_windows_refuse_never_guess() {
    let p = BigUint::from(P);
    let mut manager = TermManager::new();
    let (field, assertions) = planted_chain(&mut manager, &p, 48, None);
    // A budget so small the windows themselves budget out: the outcome
    // must be a refusal, never a verdict (the skipped-window gate).
    let outcome = check_conjunction(&manager, field, &assertions, 1 << 8);
    match outcome {
        FfOutcome::OutOfBudget { .. } | FfOutcome::InvalidModel(_) => {}
        other => panic!("a starved window split must refuse, got {other:?}"),
    }
}

// Why there is no small-prime brute-force cross-check here: routing
// through the windows requires a size whose monolithic cascade is the
// expensive path (n > 48), and exhaustive enumeration requires p^n
// small (n < 15 with p = 11). The two are structurally incompatible;
// tiny-system verdict coverage stays with `ff_oracle.rs` (exhaustive at
// tiny primes) and the corpus (release binary, the study's tables).
