//! Model-reconstruction regression for elimination/ELS obligations
//! (2026-09-13, `docs/studies/2026-09-13-extstack-reconstruction.md`).
//!
//! The bug class this file pins: `save_model` used to reconstruct
//! BVE-eliminated variables from a *positive-side* record (`bve_def`) plus a
//! default for empty sides, and ELS-substituted variables from a
//! representative-lookup pass.  Both are obligations reasoning over a
//! **partial** record:
//!
//! * a clause of `x` retired by `y`'s elimination never enters `x`'s record
//!   (the summle_X4053 `(10178 ∨ ¬11017)` falsification),
//! * an elimination whose positive clauses were strengthened away mid-scan
//!   records an *empty* side and defaulted `x = false` on the false premise
//!   that the side had been satisfied by unconditional units,
//! * a substituted variable whose representative is itself unconstrained
//!   (never branched, never eliminated) defaulted independently of its
//!   representative (`1268 ≡ ¬1267` falsified `(1267 ∨ 1268)`).
//!
//! On `summle_X4053` seed 2 the old reconstruction exported a model that
//! falsified 63 original clauses (the verdict was right — cadical agrees the
//! file is SAT; the *witness* was wrong).  The fix is the Sörensson/IJCAR'12
//! extension stack (cadical `External::extend`): every clause retired at an
//! elimination and both implications of every ELS equivalence are pushed
//! with a witness literal, and `save_model` walks them backward, flipping
//! the witness of falsified entries.
//!
//! These tests generate structured random formulas (implication chains over
//! shared variables — the shape that makes BVE, the sweep and ELS fire and
//! cross-retire obligations), solve with the inprocessing default path, and
//! verify the exported model against **all original clauses** with a
//! **totality** check — the exact property the corpus screens enforce
//! externally.  Small instances are additionally brute-force verdict-checked.

use nixie_sat::{ConfigPreset, Solver, SolverConfig, SolverResult};

/// Deterministic LCG (xorshift64*) so every regression run tests the same
/// instances; no dependency on crate test-ordering or wall-clock.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// A **planted-model** structured random formula: a hidden satisfying
/// assignment fixes every variable, then implication chains (the ELS/Sweep
/// food: bidirectional links make equivalences) and ternary clauses are
/// generated *consistently with the plant*, so every instance is
/// satisfiable by construction while still looking like hard structured
/// SAT to the solver.  The chain shape is what makes eliminations retire
/// clauses of *other* variables and the sweep/ELS fold equivalences over
/// unconstrained representatives — the obligation-crossing mechanisms the
/// old reconstruction mishandled.  Planted instances also make a
/// `Sat` verdict *checkable* (the plant itself is a witness), so a wrong
/// `Unsat` can never hide behind "instance was probably unsat".
fn gen_instance(seed: u64, vars: usize, chains: usize, extra: usize) -> (Vec<Vec<i32>>, Vec<bool>) {
    let mut rng = Lcg(seed);
    let plant: Vec<bool> = (0..vars).map(|_| rng.below(2) == 0).collect();
    let val = |v: usize| plant[v];
    let mut clauses = Vec::new();
    for _ in 0..chains {
        let mut v = rng.below(vars as u64) as usize;
        for _ in 0..(vars / 4) {
            let w = rng.below(vars as u64) as usize;
            if v == w {
                continue;
            }
            // Implication ¬v ∨ w, oriented so the plant satisfies it.
            let clause = if !val(v) || val(w) {
                vec![-((v + 1) as i32), (w + 1) as i32]
            } else {
                vec![(v + 1) as i32, -((w + 1) as i32)]
            };
            clauses.push(clause);
            // Equivalences between like-valued variables (both directions).
            if rng.below(4) == 0 && val(v) == val(w) {
                clauses.push(vec![-((v + 1) as i32), (w + 1) as i32]);
                clauses.push(vec![-((w + 1) as i32), (v + 1) as i32]);
            }
            v = w;
        }
    }
    for _ in 0..extra {
        let a = rng.below(vars as u64) as usize;
        let b = rng.below(vars as u64) as usize;
        let c = rng.below(vars as u64) as usize;
        if a == b || b == c || a == c {
            continue;
        }
        // Ternary with a planted-true literal: pick polarities randomly,
        // then force one of the three to agree with the plant.
        let mut pol = |x: usize| {
            if rng.below(2) == 0 {
                (x + 1) as i32
            } else {
                -((x + 1) as i32)
            }
        };
        let lits: Vec<i32> = vec![pol(a), pol(b), pol(c)];
        let which = rng.below(3) as usize;
        let var = [a, b, c][which];
        let lit = if val(var) {
            (var + 1) as i32
        } else {
            -((var + 1) as i32)
        };
        let mut clause = lits;
        clause[which] = lit;
        clauses.push(clause);
    }
    (clauses, plant)
}

fn solve_and_verify(seed: u64, vars: usize, chains: usize, extra: usize) -> (u64, u64, usize) {
    let (clauses, plant) = gen_instance(seed, vars, chains, extra);
    // CaDiCaL preset plus the pre-search collapse: instances this size solve
    // before the 2 000-conflict elimination clock, so the mid-search
    // schedule would never fire and the test would exercise nothing (the
    // same small-instance effect the AND-gate study recorded).  The
    // pre-search path runs the *same* eliminator, sweep and ELS machinery
    // and the same retirement/extension-stack code under test.
    let mut solver = Solver::with_config(SolverConfig {
        presearch_collapse: true,
        els_presearch: true,
        enable_equiv_substitution: true,
        // The chain structure is exactly what the lucky phase detects
        // (`lucky_ordered` over implication chains): with lucky on, these
        // instances solve before the eliminator/ELS ever run and the test
        // exercises nothing.
        enable_lucky: false,
        ..ConfigPreset::CaDiCaL.config()
    });
    let mut max_var = 0usize;
    for clause in &clauses {
        solver.add_clause_dimacs(clause);
        for &lit in clause {
            max_var = max_var.max(lit.unsigned_abs() as usize);
        }
    }
    // The plant is a concrete witness, so anything but `Sat` is a wrong
    // verdict — a far stronger check than the skipped brute force.
    let result = solver.solve();
    assert_eq!(
        result,
        SolverResult::Sat,
        "seed {seed}: planted-satisfiable instance got a non-Sat verdict"
    );
    // Generator self-check: the plant really satisfies every clause, so a
    // failure here is a test bug, not a solver bug.
    for clause in &clauses {
        assert!(
            clause
                .iter()
                .any(|&lit| plant[lit.unsigned_abs() as usize - 1] == (lit > 0)),
            "generator bug: clause {clause:?} not satisfied by the plant"
        );
    }
    match result {
        SolverResult::Sat => {
            // The property under test: the exported model is TOTAL and
            // satisfies every original clause — including the literals of
            // clauses eliminated away from the live database, which only
            // correct reconstruction can cover.
            for (i, clause) in clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let var = lit.unsigned_abs() as usize - 1;
                    let val = solver.model_value(nixie_sat::Var::new(var as u32));
                    let positive = lit > 0;
                    match val {
                        nixie_sat::LBool::True => positive,
                        nixie_sat::LBool::False => !positive,
                        nixie_sat::LBool::Undef => false,
                    }
                });
                assert!(
                    satisfied,
                    "seed {seed}: original clause #{i} {clause:?} falsified by the exported model"
                );
            }
            for v in 0..max_var {
                assert_ne!(
                    solver.model_value(nixie_sat::Var::new(v as u32)),
                    nixie_sat::LBool::Undef,
                    "seed {seed}: variable {} left unassigned in a Sat model",
                    v + 1
                );
            }
            // Verdict cross-check by brute force on the small instances
            // (large ones are not enumerable; the model check above is the
            // soundness net that carries them).
            if let Some(sat) = brute_force_sat(&clauses, max_var) {
                assert!(
                    sat,
                    "seed {seed}: solver reported Sat but brute force disagrees"
                );
            }
        }
        SolverResult::Unsat => {
            if let Some(sat) = brute_force_sat(&clauses, max_var) {
                assert!(
                    !sat,
                    "seed {seed}: solver reported Unsat but brute force finds a model"
                );
            }
        }
        // No `Unknown` arm: the pure-SAT path under test has no budget
        // limits, so an Unknown here is a wiring failure, not a verdict.
        SolverResult::Unknown => {
            panic!("seed {seed}: pure-SAT solve returned Unknown");
        }
    }
    let stats = solver.stats();
    eprintln!(
        "seed {seed}: result={result:?} bve={} defs={} subst={} oblig={} units={}",
        stats.bve_eliminated,
        stats.definition_eliminated,
        stats.substitutions,
        solver.extension_obligations(),
        stats.unit_clauses
    );
    (
        stats.bve_eliminated,
        stats.substitutions,
        solver.extension_obligations(),
    )
}

/// `None` when the instance is not brute-forceable (too many variables);
/// callers skip the verdict cross-check and rely on the model checks.
fn brute_force_sat(clauses: &[Vec<i32>], max_var: usize) -> Option<bool> {
    if max_var == 0 || max_var > 20 {
        return None;
    }
    for bits in 0u64..(1u64 << max_var) {
        let ok = clauses.iter().all(|clause| {
            clause.iter().any(|&lit| {
                let var = lit.unsigned_abs() as usize - 1;
                let assigned = (bits >> var) & 1 == 1;
                assigned == (lit > 0)
            })
        });
        if ok {
            return Some(true);
        }
    }
    Some(false)
}

#[test]
fn elimination_model_reconstruction_structured_random() {
    let mut total_eliminated = 0u64;
    let mut total_substituted = 0u64;
    let mut with_obligations = 0usize;
    for seed in 0..24u64 {
        let (eliminated, substituted, obligations) = solve_and_verify(seed, 60, 8, 120);
        total_eliminated += eliminated;
        total_substituted += substituted;
        if obligations > 0 {
            with_obligations += 1;
        }
    }
    // The regression is only meaningful if the mechanism actually fired:
    // require eliminations, equivalences, and extension-stack obligations on
    // a good fraction of instances, so a silent wiring change (e.g. the
    // passes never running under this config) fails loudly here instead of
    // vacuously passing the model checks.
    eprintln!("ELIM={total_eliminated} SUBST={total_substituted} OBLIG={with_obligations}");
    assert!(
        total_eliminated > 0,
        "no BVE eliminations fired - test not exercising the mechanism"
    );
    assert!(
        total_substituted > 0,
        "no ELS substitutions fired - test not exercising the mechanism"
    );
    assert!(
        with_obligations >= 8,
        "extension-stack obligations missing on {with_obligations}/24 instances"
    );
}

#[test]
fn elimination_model_reconstruction_larger_instances() {
    for seed in 100..112u64 {
        let (eliminated, substituted, _) = solve_and_verify(seed, 220, 14, 500);
        assert!(
            eliminated + substituted > 0,
            "seed {seed}: neither mechanism fired on a 220-var instance"
        );
    }
}
