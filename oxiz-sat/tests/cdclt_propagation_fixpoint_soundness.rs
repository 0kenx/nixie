//! Regression: `solve_with_theory` must never answer `Sat` with Boolean
//! propagation left un-run.
//!
//! The CDCL(T) loop handles a theory conflict by backtracking, learning the
//! analysed clause and putting its asserting literal on the trail – for a unit
//! lemma, a brand-new **level-0 fact**. That literal is appended *unpropagated*.
//! The theory-conflict branches used to rejoin the inner theory loop, which does
//! not run BCP; only the outer search loop does. As long as some variable was
//! still open the gap closed itself, because the next decision fell through to
//! the outer loop and propagation caught up. But when the theory conflict
//! resolved the **last** unassigned variable, `pick_branch_var` reported "all
//! assigned" and the loop went straight to `final_check`. The theory saw a
//! consistent set of atoms and said `Sat`, and `solve_with_theory` returned that
//! `Sat` over a trail on which an **original** clause was already falsified by
//! level-0 facts alone – a total model that does not satisfy the input formula,
//! on an instance that is in fact `Unsat`.
//!
//! Reference: Z3's `smt_context.cpp`, whose `final_check` is likewise only
//! reached from a state where `propagate()` has reached a fixpoint.

use oxiz_sat::{Lit, Solver, SolverConfig, SolverResult, TheoryCallback, TheoryCheckResult, Var};

/// A solver whose branching is fully deterministic.
///
/// The default configuration flips 2 % of decisions to a random polarity, which
/// is fine for search but makes a *scripted* reproduction unreliable: the shape
/// below needs every decision to take the saved phase (initially negative) so
/// the theory's lemma fires on each variable in turn. Everything else is left at
/// its default, so the code path under test is the production one.
fn deterministic_solver() -> Solver {
    Solver::with_config(SolverConfig {
        random_polarity_prob: 0.0,
        ..SolverConfig::default()
    })
}

/// A theory that forces a fixed polarity on each of a set of variables.
///
/// The lemma it reports is the unit clause "`var` must take its forced
/// polarity": whenever a literal is assigned against that polarity, the literal
/// itself is false, so `Conflict([lit.negate()])` is a well-formed, fully
/// falsified conflict clause. Every such lemma is globally valid, which makes
/// CDCL(T) over `cnf` with this theory exactly SAT of `cnf` conjoined with the
/// forced unit literals – an exactly brute-forceable oracle.
struct ForcedPolarityTheory {
    /// `forced[i] == Some(p)` pins variable `i` to polarity `p`.
    forced: Vec<Option<bool>>,
    /// Number of lemmas reported, so a test can confirm the theory really drove
    /// the search rather than the Boolean core solving it alone.
    lemmas: usize,
}

impl ForcedPolarityTheory {
    fn new(forced: Vec<Option<bool>>) -> Self {
        Self { forced, lemmas: 0 }
    }
}

impl TheoryCallback for ForcedPolarityTheory {
    fn on_assignment(&mut self, lit: Lit) -> TheoryCheckResult {
        if let Some(Some(want)) = self.forced.get(lit.var().index())
            && *want != lit.is_pos()
        {
            self.lemmas += 1;
            return TheoryCheckResult::Conflict([lit.negate()].into_iter().collect());
        }
        TheoryCheckResult::Sat
    }

    fn final_check(&mut self) -> TheoryCheckResult {
        TheoryCheckResult::Sat
    }

    fn on_backtrack(&mut self, _level: u32) {}
}

/// Every non-deleted original clause must be satisfied by the reported model.
fn model_satisfies(solver: &Solver, clauses: &[Vec<Lit>]) -> bool {
    clauses.iter().all(|c| {
        c.iter().any(|l| {
            let v = solver.model_value(l.var());
            if l.is_pos() {
                v.is_true()
            } else {
                v.is_false()
            }
        })
    })
}

/// The minimal reproducer, reduced from a QF_LIA instance
/// (`x0 = -1 ∧ (x1 = x0-1 ∨ x1 = x0) ∧ (x2 = x1-1 ∨ x2 = x1) ∧ x2 = 0`) all the
/// way down to the Boolean core plus a three-line stub theory.
///
/// The theory pins `a`, `b` and `c` to **true**; the single original clause says
/// at least one of them is false. The instance is therefore `Unsat`.
///
/// The default decision polarity is negative, so the search decides `¬a`, the
/// theory reports the unit lemma `a`, and the loop backtracks to level 0 and
/// pins `a` there – repeating for `b` and then `c`. That third lemma assigns the
/// last open variable, so pre-fix the very next step was `final_check`, which
/// answered `Sat`, and the model `a = b = c = true` falsified the clause.
#[test]
fn theory_unit_lemma_on_last_open_var_must_not_yield_sat() {
    let mut solver = deterministic_solver();
    let a = solver.new_var();
    let b = solver.new_var();
    let c = solver.new_var();

    assert!(solver.add_clause([Lit::neg(a), Lit::neg(b), Lit::neg(c)]));

    let mut theory = ForcedPolarityTheory::new(vec![Some(true), Some(true), Some(true)]);
    let result = solver.solve_with_theory(&mut theory);

    assert!(
        theory.lemmas > 0,
        "the stub theory must actually have driven the search"
    );
    assert_eq!(
        result,
        SolverResult::Unsat,
        "the theory pins a, b and c to true while (¬a ∨ ¬b ∨ ¬c) forbids it: \
         the only sound verdict is Unsat"
    );
}

/// Companion of the above with a satisfiable Boolean part: the verdict must be
/// `Sat` **and** the reported model must satisfy the original clauses.
#[test]
fn theory_unit_lemma_sat_model_satisfies_every_original_clause() {
    let mut solver = deterministic_solver();
    let a = solver.new_var();
    let b = solver.new_var();
    let c = solver.new_var();

    // (¬a ∨ ¬b ∨ c) is satisfied by a = b = c = true, which the theory forces.
    let clauses = vec![
        vec![Lit::neg(a), Lit::neg(b), Lit::pos(c)],
        vec![Lit::pos(a), Lit::pos(b)],
    ];
    for c in &clauses {
        assert!(solver.add_clause(c.iter().copied()));
    }

    let mut theory = ForcedPolarityTheory::new(vec![Some(true), Some(true), Some(true)]);
    let result = solver.solve_with_theory(&mut theory);

    assert_eq!(result, SolverResult::Sat);
    assert!(
        model_satisfies(&solver, &clauses),
        "solve_with_theory returned Sat over a model that falsifies an original clause"
    );
    for (i, want) in [(a, true), (b, true), (c, true)] {
        let v = solver.model_value(i);
        assert_eq!(
            v.is_true(),
            want,
            "the model must respect the theory's forced polarity for var {}",
            i.index()
        );
    }
}

/// Deterministic SplitMix64 – no external `rand` dependency, no wall-clock input.
struct Rng(u64);
impl Rng {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
}

/// Bounded, deterministic randomised differential test of the CDCL(T) path
/// against an exact brute-force oracle.
///
/// Because every lemma the stub theory reports is a globally valid unit clause,
/// `cnf` solved under it is satisfiable exactly when some total assignment
/// satisfies `cnf` and agrees with all forced polarities – enumerable in `2^n`.
/// Both verdicts are therefore assertable, and every `Sat` additionally has its
/// model checked against the clauses. Zero mismatches is the contract.
///
/// The family is deliberately theory-dominated – few, wide clauses and most
/// variables pinned – so the search is driven by unit lemmas rather than by BCP,
/// which is what puts pressure on the propagation-fixpoint invariant. Against
/// the pre-fix loop this seed found 24 unsound verdicts in 20 000 instances; it
/// runs in well under a second.
#[test]
fn cdclt_random_differential_vs_brute_force() {
    const NUM_VARS: usize = 6;
    const INSTANCES: usize = 20000;

    let mut rng = Rng(0x51ED_270B_2C09_9A57);
    let mut mismatches = 0usize;
    let mut unknown = 0usize;
    let mut decided = 0usize;
    let mut sat_seen = 0usize;
    let mut unsat_seen = 0usize;
    let mut first_bad = String::new();

    for _ in 0..INSTANCES {
        // Random CNF: 1..=3 clauses of 3..=4 distinct literals over NUM_VARS.
        let num_clauses = 1 + rng.below(3) as usize;
        let mut cnf: Vec<Vec<Lit>> = Vec::with_capacity(num_clauses);
        for _ in 0..num_clauses {
            let width = 3 + rng.below(2) as usize;
            let mut lits: Vec<Lit> = Vec::with_capacity(width);
            while lits.len() < width {
                let v = rng.below(NUM_VARS as u64) as u32;
                if lits.iter().any(|l| l.var().index() as u32 == v) {
                    continue;
                }
                let var = Var::new(v);
                lits.push(if rng.below(2) == 0 {
                    Lit::pos(var)
                } else {
                    Lit::neg(var)
                });
            }
            cnf.push(lits);
        }

        // Random forced polarities on a subset of the variables.
        let forced: Vec<Option<bool>> = (0..NUM_VARS)
            .map(|_| match rng.below(6) {
                0 => None,
                _ => Some(rng.below(2) == 0),
            })
            .collect();

        // Exact oracle over all 2^NUM_VARS assignments.
        let mut oracle_sat = false;
        for mask in 0u32..(1u32 << NUM_VARS) {
            let val = |v: usize| (mask >> v) & 1 == 1;
            if forced
                .iter()
                .enumerate()
                .any(|(v, f)| matches!(f, Some(p) if *p != val(v)))
            {
                continue;
            }
            if cnf.iter().all(|c| {
                c.iter().any(|l| {
                    if l.is_pos() {
                        val(l.var().index())
                    } else {
                        !val(l.var().index())
                    }
                })
            }) {
                oracle_sat = true;
                break;
            }
        }

        let mut solver = deterministic_solver();
        for _ in 0..NUM_VARS {
            solver.new_var();
        }
        let mut trivially_unsat = false;
        for c in &cnf {
            if !solver.add_clause(c.iter().copied()) {
                trivially_unsat = true;
            }
        }

        let mut theory = ForcedPolarityTheory::new(forced.clone());
        let result = solver.solve_with_theory(&mut theory);

        let bad = match result {
            SolverResult::Unknown => {
                unknown += 1;
                continue;
            }
            SolverResult::Sat => {
                sat_seen += 1;
                decided += 1;
                !oracle_sat || trivially_unsat || !model_satisfies(&solver, &cnf)
            }
            SolverResult::Unsat => {
                unsat_seen += 1;
                decided += 1;
                oracle_sat
            }
        };
        if bad {
            mismatches += 1;
            if first_bad.is_empty() {
                first_bad =
                    format!("cnf={cnf:?} forced={forced:?} got={result:?} oracle_sat={oracle_sat}");
            }
        }
    }

    assert_eq!(
        mismatches, 0,
        "UNSOUND: {mismatches}/{INSTANCES} CDCL(T) verdicts disagreed with brute force \
         (decided={decided}, unknown={unknown}); first: {first_bad}"
    );
    assert_eq!(
        unknown, 0,
        "no instance in this bounded family should be Unknown"
    );
    // Both verdicts must actually be exercised, or the test proves nothing.
    assert!(
        sat_seen > 0 && unsat_seen > 0,
        "sat={sat_seen} unsat={unsat_seen}"
    );
}
