//! Soundness tests for the analyze-time OTFS arm (`NIXIE_OTFS`,
//! cadical `analyze.cpp` on-the-fly strengthening).
//!
//! The arm rewrites antecedent clauses **in place** during 1-UIP resolution
//! (dropping the pivot literal and level-0-falsified literals) and restarts
//! the analysis from the strengthened clause. Every failure mode is a
//! soundness bug, not a performance bug, so these tests pair OTFS-on and
//! OTFS-off solves over deterministic random CNFs and demand exact verdict
//! agreement, model validity for every `sat`, and non-vacuous firing
//! (the counters must be non-zero on instances large enough to resolve
//! through clauses the trigger can reach).

use crate::LBool;
use crate::literal::Lit;
use crate::solver::Solver;

/// Deterministic xorshift64* — stable across platforms and releases so a
/// failure reproduces exactly.
struct Rng(u64);
impl Rng {
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

/// One random CNF with redundancy structure: every base clause also appears
/// as literal-supersets (c ∪ {extra}), the shape that makes the OTFS trigger
/// (`accumulated resolvent < antecedent size`) reachable — circuit-class
/// formulas are exactly this shape (507 904 near-duplicate 13-clauses).
fn random_cnf(rng: &mut Rng, vars: usize, clauses: usize, len: usize) -> Vec<Vec<i32>> {
    let mut out = Vec::with_capacity(clauses * 2);
    for _ in 0..clauses {
        let mut c = Vec::with_capacity(len);
        while c.len() < len {
            let v = rng.below(vars as u64) as i32 + 1;
            let sign = if rng.below(2) == 0 { 1 } else { -1 };
            let lit = sign * v;
            if !c.contains(&lit) && !c.contains(&-lit) {
                c.push(lit);
            }
        }
        out.push(c.clone());
        // Redundant supersets of `c` (subsumed by it): the antecedent walk
        // then resolves through clauses the resolvent can be smaller than.
        if rng.below(3) == 0 {
            let mut wide = c.clone();
            while wide.len() < len + 2 {
                let v = rng.below(vars as u64) as i32 + 1;
                let sign = if rng.below(2) == 0 { 1 } else { -1 };
                let lit = sign * v;
                if !wide.contains(&lit) && !wide.contains(&-lit) {
                    wide.push(lit);
                }
            }
            out.push(wide);
        }
    }
    out
}

fn build(solver: &mut Solver, cnf: &[Vec<i32>]) {
    for clause in cnf {
        let lits: Vec<Lit> = clause.iter().map(|&d| Lit::from_dimacs(d)).collect();
        solver.add_clause(lits);
    }
}

fn model_satisfies(solver: &Solver, cnf: &[Vec<i32>]) -> bool {
    let model = solver.model();
    for clause in cnf {
        let ok = clause.iter().any(|&d| {
            let vi = d.unsigned_abs() as usize - 1;
            let val = model.get(vi).copied().unwrap_or(LBool::Undef);
            match val {
                LBool::True => d > 0,
                LBool::False => d < 0,
                LBool::Undef => false,
            }
        });
        if !ok {
            return false;
        }
    }
    true
}

/// Paired differential: verdicts must agree exactly on every instance, and
/// every `sat` model must satisfy the input under BOTH arms (an OTFS-introduced
/// unsoundness shows up here as a verdict flip or an invalid model).
#[test]
fn otfs_verdict_agreement_random_cnf() {
    let mut rng = Rng(0x07F5_5EED);
    let mut fired = 0u64;
    let instances = 220;
    for i in 0..instances {
        // Mixed shapes: small unsat cores (high clause density), satisfiable
        // sparse ones, and wider clauses (4-5 lits exercise the
        // `antecedent > 2` gate on every resolution).
        // Shapes measured (probe) to reach the search path and fire the
        // OTFS trigger; smaller ones are fully solved in preprocessing.
        let (vars, clauses, len) = match i % 4 {
            0 => (44, 190, 3),
            1 => (48, 205, 3),
            2 => (40, 170, 3),
            _ => (52, 230, 3),
        };
        let cnf = random_cnf(&mut rng, vars, clauses, len);

        let mut off = Solver::with_config(crate::ConfigPreset::CaDiCaL.config());
        build(&mut off, &cnf);
        let verdict_off = off.solve();

        let mut on = Solver::with_config(crate::ConfigPreset::CaDiCaL.config());
        on.set_otfs(true);
        build(&mut on, &cnf);
        let verdict_on = on.solve();

        assert_eq!(
            format!("{verdict_off:?}"),
            format!("{verdict_on:?}"),
            "verdict disagreement on instance {i}: {cnf:?}"
        );
        if format!("{verdict_off:?}") == "Sat" {
            assert!(
                model_satisfies(&off, &cnf),
                "OTFS-OFF model invalid on instance {i}"
            );
            assert!(
                model_satisfies(&on, &cnf),
                "OTFS-ON model invalid on instance {i}: {cnf:?}"
            );
        }
        fired += on.stats().otfs_strengthened + on.stats().otfs_subsumed;
    }
    // Non-vacuous: the arm actually fired across the batch (else the
    // agreement result carries no information about the new code paths).
    assert!(fired > 0, "OTFS never fired across {instances} instances");
}

/// The OTFS special cases: when the self-subsumption derives a unit or the
/// empty clause the analysis returns it directly. Exercised via denser CNFs
/// where resolutions shrink antecedents below two live literals.
#[test]
fn otfs_unit_and_empty_paths_agree() {
    let mut rng = Rng(0xDECA_FBAD);
    let mut fired = 0u64;
    for i in 0..160 {
        let (vars, clauses, len) = match i % 3 {
            0 => (46, 198, 3),
            1 => (50, 218, 3),
            _ => (42, 182, 3),
        };
        let cnf = random_cnf(&mut rng, vars, clauses, len);
        let mut off = Solver::with_config(crate::ConfigPreset::CaDiCaL.config());
        build(&mut off, &cnf);
        let v_off = format!("{:?}", off.solve());
        let mut on = Solver::with_config(crate::ConfigPreset::CaDiCaL.config());
        on.set_otfs(true);
        build(&mut on, &cnf);
        let v_on = format!("{:?}", on.solve());
        assert_eq!(v_off, v_on, "instance {i}: {cnf:?}");
        if v_on == "Sat" {
            assert!(model_satisfies(&on, &cnf), "instance {i}: {cnf:?}");
        }
        fired += on.stats().otfs_strengthened + on.stats().otfs_subsumed;
    }
    assert!(fired > 0);
}

/// Proof attachment must disable the arm: the pivot drop is justified by
/// resolution against the in-flight resolvent, which no attached proof can
/// replay. With DRAT enabled the trajectory must stay bit-identical to the
/// arm-off run (the trigger is never taken).
#[test]
fn otfs_inert_under_proof() {
    use std::sync::Arc;
    let mut rng = Rng(0x1234_ABCD);
    let path = std::env::temp_dir().join("nixie_sat_otfs_inert_under_proof.drat");
    for _ in 0..40 {
        let cnf = random_cnf(&mut rng, 46, 200, 3);
        let mut reference = Solver::with_config(crate::ConfigPreset::CaDiCaL.config());
        reference
            .enable_drat_proof(&path)
            .expect("enable DRAT proof");
        build(&mut reference, &cnf);
        let v_ref = format!("{:?}", reference.solve());
        let c_ref = reference.stats().conflicts;
        let d_ref = reference.stats().decisions;
        let _ = std::fs::remove_file(&path);

        let mut on = Solver::with_config(crate::ConfigPreset::CaDiCaL.config());
        on.set_otfs(true);
        on.enable_drat_proof(&path).expect("enable DRAT proof");
        build(&mut on, &cnf);
        let v_on = format!("{:?}", on.solve());
        assert_eq!(v_ref, v_on);
        assert_eq!(
            c_ref,
            on.stats().conflicts,
            "trajectory changed under proof"
        );
        assert_eq!(d_ref, on.stats().decisions);
        assert_eq!(0, on.stats().otfs_strengthened, "OTFS fired under proof");
        let _ = std::fs::remove_file(&path);
    }
    let _ = Arc::new(0u8); // keep the `use` honest if cfg strips it
}
