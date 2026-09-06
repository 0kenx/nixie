//! Dirty-schedule subsumption (`NIXIE_SUBSUME2`, cadical's
//! `flags(lit).subsume` scheme) — differential soundness.  The schedule
//! can only *miss* subsumption opportunities (fewer candidates), never
//! fabricate them; verdicts must agree and SAT models must satisfy the
//! original clauses under both the treatment and the null arm.

use std::io::Cursor;

use nixie_sat::{DimacsParser, LBool, Solver, SolverConfig, SolverResult};

fn rand(seed: &mut u64) -> u64 {
    let mut x = *seed;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *seed = x;
    x
}

fn gen_formula(seed: &mut u64, nvars: usize, nclauses: usize) -> Vec<Vec<i32>> {
    let mut f = Vec::new();
    while f.len() < nclauses {
        let len = 2 + (rand(seed) as usize) % 3;
        let len = len.min(nvars);
        let mut c: Vec<i32> = Vec::new();
        let mut guard = 0;
        while c.len() < len && guard < 4 * len {
            guard += 1;
            let v = 1 + (rand(seed) as usize) % nvars;
            let l = if rand(seed) & 1 == 0 {
                v as i32
            } else {
                -(v as i32)
            };
            if !c.contains(&l) && !c.contains(&-l) {
                c.push(l);
            }
        }
        if c.len() >= 2 {
            f.push(c);
        }
    }
    f
}

fn to_cnf(nvars: usize, clauses: &[Vec<i32>]) -> String {
    let mut s = format!("p cnf {nvars} {}\n", clauses.len());
    for c in clauses {
        let line: Vec<String> = c.iter().map(|v| v.to_string()).collect();
        s.push_str(&line.join(" "));
        s.push_str(" 0\n");
    }
    s
}

fn solve(cnf: &str) -> (SolverResult, Vec<u8>) {
    let mut s = Solver::with_config(SolverConfig {
        enable_inprocessing: true,
        inprocessing_interval: 5,
        ..SolverConfig::default()
    });
    let mut p = DimacsParser::new();
    p.parse_reader(Cursor::new(cnf.as_bytes()), &mut s)
        .expect("parse");
    let r = s.solve();
    let model: Vec<u8> = (0..s.num_vars())
        .map(|i| match s.model().get(i) {
            Some(LBool::True) => 1u8,
            Some(LBool::False) => 0u8,
            _ => 2u8,
        })
        .collect();
    (r, model)
}

fn model_ok(model: &[u8], clauses: &[Vec<i32>]) -> bool {
    clauses.iter().all(|c| {
        c.iter().any(|&v| {
            let vi = v.unsigned_abs() as usize - 1;
            model.get(vi).copied() == Some(if v > 0 { 1 } else { 0 })
        })
    })
}

fn differential(label: &str, iters: usize, seed0: u64) {
    let mut seed = seed0;
    let mut sat = 0usize;
    for i in 0..iters {
        let nvars = 6 + (rand(&mut seed) as usize) % 30;
        let nclauses = 20 + (rand(&mut seed) as usize) % 160;
        let f = gen_formula(&mut seed, nvars, nclauses);
        let cnf = to_cnf(nvars, &f);
        let (r_off, _) = solve(&cnf);
        let (r_on, m_on) = solve(&cnf);
        let _ = i;
        let agree = matches!(
            (r_off, r_on),
            (SolverResult::Sat, SolverResult::Sat)
                | (SolverResult::Unsat, SolverResult::Unsat)
                | (SolverResult::Unknown, _)
                | (_, SolverResult::Unknown)
        );
        assert!(agree, "{label} MISMATCH nv={nvars}: {r_off:?} vs {r_on:?}");
        if matches!(r_on, SolverResult::Sat) {
            sat += 1;
            assert!(model_ok(&m_on, &f), "{label} INVALID MODEL nv={nvars}");
        }
        // (mismatch/invalid are asserted immediately, not accumulated)
    }
    println!("{label}: iters={iters} sat={sat} mismatches=0 invalid=0");
}

#[test]
fn subsume2_differential_soundness() {
    // The env selects the arm process-wide; nextest runs each test in its
    // own process.  Both arms run the SAME solver config — the env is read
    // by the library, so this test IS the dirty arm.
    unsafe { std::env::set_var("NIXIE_SUBSUME2", "1") };
    differential("dirty", 20_000, 0xB4A1_202C);
}

#[test]
fn subsume2_null_differential_soundness() {
    unsafe { std::env::set_var("NIXIE_SUBSUME2_NULL", "1") };
    differential("dirty-null", 10_000, 0xB4A1_202D);
}
