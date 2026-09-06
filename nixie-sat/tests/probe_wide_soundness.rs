//! Probe-schedule widening (`NIXIE_PROBE_WIDE`, default on since
//! 2026-09-07): the candidate queue includes variables with binaries in
//! both polarities (the legacy schedule skipped them).  Only the ORDER
//! and COVERAGE of probe candidates changes — the probe itself (assign →
//! propagate → check) is identical, so soundness is structural.  This
//! fuzz is the belt-and-suspenders check.

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
        let mut c: Vec<i32> = Vec::new();
        let mut g = 0;
        while c.len() < len.min(nvars) && g < 4 * len {
            g += 1;
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
    let m = (0..s.num_vars())
        .map(|i| match s.model().get(i) {
            Some(LBool::True) => 1u8,
            Some(LBool::False) => 0u8,
            _ => 2u8,
        })
        .collect();
    (r, m)
}

fn model_ok(m: &[u8], f: &[Vec<i32>]) -> bool {
    f.iter().all(|c| {
        c.iter().any(|&v| {
            let vi = v.unsigned_abs() as usize - 1;
            m.get(vi).copied() == Some(if v > 0 { 1 } else { 0 })
        })
    })
}

#[test]
fn probe_wide_differential_soundness() {
    // Safety: nextest runs each test in its own process.
    unsafe { std::env::set_var("NIXIE_PROBE_WIDE", "1") };
    let mut seed = 0xB4A1_202E_u64;
    let mut sat = 0;
    for i in 0..20_000 {
        let nv = 6 + (rand(&mut seed) as usize) % 30;
        let nc = 20 + (rand(&mut seed) as usize) % 160;
        let f = gen_formula(&mut seed, nv, nc);
        let body: String = f
            .iter()
            .map(|c| {
                c.iter()
                    .map(|v| v.to_string())
                    .collect::<Vec<_>>()
                    .join(" ")
                    + " 0\n"
            })
            .collect();
        let cnf = format!("p cnf {nv} {}\n{}", f.len(), body);
        let (r, m) = solve(&cnf);
        if matches!(r, SolverResult::Sat) {
            sat += 1;
            assert!(model_ok(&m, &f), "INVALID MODEL iter={i} nv={nv}");
        }
        assert!(
            !matches!(r, SolverResult::Unknown) || i < 0,
            "unexpected Unknown"
        );
    }
    println!("probe-wide: 20000 iters, sat={sat}, all models valid");
}
