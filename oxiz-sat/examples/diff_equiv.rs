//! Differential correctness fuzz for equivalent-literal substitution.
//! Generates random CNFs (mix of binary + ternary clauses so the binary
//! implication graph has SCCs), solves each via the SAME DimacsParser path
//! with EQUIV off and EQUIV on, and requires: (a) SAT/UNSAT agreement and
//! (b) any SAT model satisfies every original clause. Exits non-zero on any
//! divergence.
use oxiz_sat::{DimacsParser, LBool, Solver, SolverConfig};
use std::io::Cursor;

fn rand(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

fn to_cnf(nvars: usize, clauses: &[Vec<i32>]) -> String {
    let mut s = format!("p cnf {nvars} {}\n", clauses.len());
    for c in clauses {
        for &v in c {
            s.push_str(&format!("{v} "));
        }
        s.push_str("0\n");
    }
    s
}

fn gen_formula(seed: &mut u64, nvars: usize, nclauses: usize) -> Vec<Vec<i32>> {
    let mut out = Vec::new();
    for _ in 0..nclauses {
        let len = if rand(seed) % 10 < 4 { 2 } else { 3 };
        let mut c = Vec::new();
        while c.len() < len {
            let v = (rand(seed) as usize) % nvars + 1;
            let lit: i32 = if rand(seed) % 2 == 0 { v as i32 } else { -(v as i32) };
            if !c.contains(&lit) && !c.contains(&-lit) {
                c.push(lit);
            }
        }
        out.push(c);
    }
    out
}

fn solve(equiv: bool, bve: bool, cnf: &str) -> (oxiz_sat::SolverResult, Vec<u8>) {
    let mut cfg = SolverConfig::default();
    cfg.enable_equiv_substitution = equiv;
    cfg.enable_bve = bve;
    let mut s = Solver::with_config(cfg);
    let mut p = DimacsParser::new();
    p.parse_reader(Cursor::new(cnf.as_bytes()), &mut s).unwrap();
    let r = s.solve();
    let model: Vec<u8> = (0..s.num_vars())
        .map(|i| match s.model().get(i) {
            Some(LBool::True) => 1u8,
            Some(LBool::False) => 0u8,
            _ => 2u8, // undef
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

fn main() {
    let iters: u64 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(5000);
    let mut seed: u64 = 0xC0FFEE;
    let mut mismatch = 0usize;
    let mut invalid = 0usize;
    let mut sat = 0usize;
    for i in 0..iters {
        let nvars = 5 + (rand(&mut seed) as usize) % 25;
        let nclauses = 8 + (rand(&mut seed) as usize) % 60;
        let f = gen_formula(&mut seed, nvars, nclauses);
        let cnf = to_cnf(nvars, &f);
        let (r_off, _) = solve(false, false, &cnf);
        let (r_on, m_on) = solve(false, true, &cnf);
        let agree = matches!((r_off, r_on),
            (oxiz_sat::SolverResult::Sat, oxiz_sat::SolverResult::Sat)
            | (oxiz_sat::SolverResult::Unsat, oxiz_sat::SolverResult::Unsat));
        if !agree {
            mismatch += 1;
            std::fs::write("/tmp/fail_equiv.cnf", &cnf).ok();
            eprintln!("MISMATCH nv={nvars} nc={nclauses} off={r_off:?} on={r_on:?}");
            if mismatch >= 3 { break; }
            if mismatch <= 3 {
                eprintln!("MISMATCH iter={i} nv={nvars} nc={nclauses}: off={r_off:?} on={r_on:?}");
            }
            continue;
        }
        if matches!(r_on, oxiz_sat::SolverResult::Sat) {
            sat += 1;
            if !model_ok(&m_on, &f) {
                invalid += 1;
                if invalid == 1 {
                    std::fs::write("/tmp/fail_equiv.cnf", &cnf).ok();
                    eprintln!("dumped invalid-model case to /tmp/fail_equiv.cnf  model={m_on:?}");
                }
                if invalid <= 3 {
                    eprintln!("INVALID MODEL iter={i} nv={nvars} nc={nclauses}: model={m_on:?}");
                }
            }
        }
    }
    println!("iters={iters} sat={sat} mismatches={mismatch} invalid_models={invalid}");
    if mismatch > 0 || invalid > 0 {
        std::process::exit(1);
    }
}
