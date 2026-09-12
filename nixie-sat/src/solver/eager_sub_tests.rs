//! Soundness tests for the eager-subsumption arm (`NIXIE_EAGER_SUB`,
//! cadical `analyze.cpp::eagerly_subsume_recently_learned_clauses`).
//!
//! The arm retires learned clauses subsumed by each freshly learned clause
//! (newest-first, ≤ 20 candidates). Sound by construction — both clauses
//! are consequences of the formula and the subsumer is strictly stronger —
//! but the retirement path (live trail reasons re-pointed to `Decision`,
//! watch/BIG purges) and the trajectory change deserve differential
//! verification: verdicts must agree and models must be valid.

use crate::LBool;
use crate::literal::Lit;
use crate::solver::Solver;

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
            match model.get(vi).copied().unwrap_or(LBool::Undef) {
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

fn random_cnf(rng: &mut Rng, vars: usize, clauses: usize, len: usize) -> Vec<Vec<i32>> {
    let mut out = Vec::with_capacity(clauses);
    for _ in 0..clauses {
        let mut c = Vec::with_capacity(len);
        while c.len() < len {
            let v = rng.below(vars as u64) as i32 + 1;
            let lit = if rng.below(2) == 0 { v } else { -v };
            if !c.contains(&lit) && !c.contains(&-lit) {
                c.push(lit);
            }
        }
        out.push(c);
    }
    out
}

#[test]
fn eager_sub_verdict_agreement_random_cnf() {
    let mut rng = Rng(0x0EA7_0B50);
    let mut removed = 0u64;
    for i in 0..240 {
        let (vars, clauses, len) = match i % 4 {
            0 => (44, 190, 3),
            1 => (48, 205, 3),
            2 => (40, 170, 3),
            _ => (52, 230, 3),
        };
        let cnf = random_cnf(&mut rng, vars, clauses, len);
        let mut off = Solver::with_config(crate::ConfigPreset::CaDiCaL.config());
        build(&mut off, &cnf);
        let v_off = format!("{:?}", off.solve());
        let mut on = Solver::with_config(crate::ConfigPreset::CaDiCaL.config());
        on.set_eager_sub(true);
        build(&mut on, &cnf);
        let v_on = format!("{:?}", on.solve());
        assert_eq!(v_off, v_on, "instance {i}: {cnf:?}");
        if v_on == "Sat" {
            assert!(
                model_satisfies(&on, &cnf),
                "EAGER-SUB model invalid on instance {i}: {cnf:?}"
            );
        }
        removed += on.stats().eager_sub_removed;
    }
    assert!(removed > 0, "eager subsumption never fired");
}

/// The subset check itself: a planted duplicate of a to-be-learned shape
/// must be retired. Constructed directly: learn two clauses where the
/// second subsumes the first by construction is search-dependent, so this
/// tests the checker through the public path with a forced pair — the
/// random differential above carries the load; here we only pin that the
/// stats counters exist and stay consistent (tried >= removed).
#[test]
fn eager_sub_counters_consistent() {
    let mut rng = Rng(0xC0DE_1234);
    for _ in 0..40 {
        let cnf = random_cnf(&mut rng, 46, 200, 3);
        let mut on = Solver::with_config(crate::ConfigPreset::CaDiCaL.config());
        on.set_eager_sub(true);
        build(&mut on, &cnf);
        let _ = on.solve();
        assert!(on.stats().eager_sub_tried >= on.stats().eager_sub_removed);
    }
}
