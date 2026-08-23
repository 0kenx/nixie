//! Differential soundness fuzz for structured bounded variable addition.
//!
//! Random CNFs solved twice through the identical parser path — SBVA off
//! vs on — requiring (a) verdict agreement and (b) any SAT model of the
//! SBVA arm to satisfy every ORIGINAL clause.  The pass's encoding is
//! equisatisfiable and model-preserving in both directions by construction
//! (`oxiz-sat/src/solver/bva.rs`); this fuzz is the executable check of
//! that argument, run against the implementation as it evolves.

#![allow(clippy::unwrap_used)]

use oxiz_sat::{DimacsParser, LBool, Solver, SolverConfig, SolverResult};
use std::io::Cursor;

fn rand(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

fn gen_formula(seed: &mut u64, nvars: usize, nclauses: usize, wide: bool) -> Vec<Vec<i32>> {
    let mut out = Vec::new();
    for _ in 0..nclauses {
        // Wide clauses exercise larger common sets G; short ones fill the
        // pair index the way real corpora do.
        // Cap at nvars: a clause cannot exceed one literal per variable,
        // and the fill loop below is rejection sampling — an unreachable
        // len would spin forever (the exact trap the first version of this
        // generator fell into: nv=5 with a len-9 wide clause).
        let len = if wide {
            3 + (rand(seed) as usize) % 8
        } else if rand(seed) % 10 < 4 {
            2
        } else {
            3
        }
        .min(nvars);
        let mut c = Vec::new();
        // A shared "spine" of literals makes mergeable groups common: with
        // probability 1/2, reuse a small fixed pool so groups of >= 3
        // clauses share >= 2 literals.
        let pool = 3.min(len);
        if rand(seed).is_multiple_of(2) {
            for k in 0..pool {
                let v = (rand(seed) as usize) % 4 + 1; // vars 1..4 as spine
                let lit = if rand(seed).is_multiple_of(2) {
                    v as i32
                } else {
                    -(v as i32)
                };
                if !c.contains(&lit) && !c.contains(&-lit) {
                    c.push(lit);
                }
                let _ = k;
            }
        }
        while c.len() < len {
            let v = (rand(seed) as usize) % nvars + 1;
            let lit: i32 = if rand(seed).is_multiple_of(2) {
                v as i32
            } else {
                -(v as i32)
            };
            if !c.contains(&lit) && !c.contains(&-lit) {
                c.push(lit);
            }
        }
        out.push(c);
    }
    out
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

fn solve(sbva: bool, cnf: &str) -> (SolverResult, Vec<u8>, usize) {
    let cfg = SolverConfig {
        enable_sbva: sbva,
        ..SolverConfig::default()
    };
    let mut s = Solver::with_config(cfg);
    let mut p = DimacsParser::new();
    p.parse_reader(Cursor::new(cnf.as_bytes()), &mut s).unwrap();
    let r = s.solve();
    let model: Vec<u8> = (0..s.num_vars())
        .map(|i| match s.model().get(i) {
            Some(LBool::True) => 1u8,
            Some(LBool::False) => 0u8,
            _ => 2u8,
        })
        .collect();
    (r, model, s.num_vars())
}

fn model_ok(model: &[u8], clauses: &[Vec<i32>]) -> bool {
    clauses.iter().all(|c| {
        c.iter().any(|&v| {
            let vi = v.unsigned_abs() as usize - 1;
            model.get(vi).copied() == Some(if v > 0 { 1 } else { 0 })
        })
    })
}

#[test]
fn sbva_differential_soundness() {
    // The spine-pool generator makes mergeable groups dense; the pure-random
    // tail keeps tautological/subsumed shapes rare but present.
    let mut seed: u64 = 0xB4A1_2023;
    let (mut mismatch, mut invalid, mut sat, mut introduced_seen) = (0usize, 0usize, 0usize, false);
    let iters = 30_000;
    for i in 0..iters {
        let nvars = 5 + (rand(&mut seed) as usize) % 25;
        let nclauses = 8 + (rand(&mut seed) as usize) % 80;
        let wide = rand(&mut seed).is_multiple_of(2);
        let f = gen_formula(&mut seed, nvars, nclauses, wide);
        let cnf = to_cnf(nvars, &f);
        let (r_off, _, _) = solve(false, &cnf);
        let (r_on, m_on, vars_on) = solve(true, &cnf);
        if vars_on > nvars {
            introduced_seen = true;
        }
        let agree = matches!(
            (r_off, r_on),
            (SolverResult::Sat, SolverResult::Sat)
                | (SolverResult::Unsat, SolverResult::Unsat)
                | (SolverResult::Unknown, _)
                | (_, SolverResult::Unknown)
        );
        if !agree {
            mismatch += 1;
            if mismatch <= 3 {
                eprintln!("MISMATCH iter={i} nv={nvars}: off={r_off:?} on={r_on:?}");
            }
            continue;
        }
        if matches!(r_on, SolverResult::Sat) {
            sat += 1;
            // Model must satisfy the ORIGINAL clauses (model-preservation).
            if !model_ok(&m_on, &f) {
                invalid += 1;
                if invalid <= 3 {
                    eprintln!("INVALID MODEL iter={i} nv={nvars}");
                }
            }
        }
    }
    println!(
        "iters={iters} sat={sat} mismatches={mismatch} invalid_models={invalid} introductions_occurred={introduced_seen}"
    );
    assert_eq!(mismatch, 0);
    assert_eq!(invalid, 0);
    // The fuzz is vacuous unless the generator actually triggers BVA.
    assert!(introduced_seen, "generator never triggered an introduction");
}
