//! Gate-modulo forward subsumption (`NIXIE_GATE_SUBSUME`) — differential
//! soundness hunter/regression: verdicts must agree with the env-off
//! base, and SAT models must satisfy the ORIGINAL clauses.  The
//! generator is equivalence-dense (explicit equivalence pairs/chains +
//! shared-tail spine groups + random fillers) — the shape the pass's
//! class-modulo containment feeds on.

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
    let mut f: Vec<Vec<i32>> = Vec::new();
    let nlit = |v: usize, pos: bool| -> i32 { if pos { v as i32 } else { -(v as i32) } };
    // Equivalence pairs/chains: v ≡ w via both binary directions.  These
    // feed the SCC classes the pass maps through.
    let pairs = 1 + (rand(seed) as usize) % (nvars / 3).max(1);
    for _ in 0..pairs {
        let a = 1 + (rand(seed) as usize) % nvars;
        let b = 1 + (rand(seed) as usize) % nvars;
        if a == b {
            continue;
        }
        f.push(vec![nlit(a, false), nlit(b, true)]);
        f.push(vec![nlit(a, true), nlit(b, false)]);
    }
    // Spine groups: clauses sharing a common core, extended by extras —
    // subsumption-dense (core-only or core+1 clauses subsume their
    // wider siblings once classes fold the cores together).
    let spines = 1 + (rand(seed) as usize) % 3;
    for _ in 0..spines {
        let core_len = 1 + (rand(seed) as usize) % 2;
        let mut core: Vec<i32> = Vec::new();
        while core.len() < core_len {
            let v = 1 + (rand(seed) as usize) % nvars;
            let l = nlit(v, rand(seed) & 1 == 0);
            if !core.contains(&l) && !core.contains(&-l) {
                core.push(l);
            }
        }
        let k = 2 + (rand(seed) as usize) % 4;
        for _ in 0..k {
            let mut c = core.clone();
            let extras = 1 + (rand(seed) as usize) % 3;
            for _ in 0..extras {
                let v = 1 + (rand(seed) as usize) % nvars;
                let l = nlit(v, rand(seed) & 1 == 0);
                if !c.contains(&l) && !c.contains(&-l) {
                    c.push(l);
                }
            }
            f.push(c);
        }
    }
    // AND-gate twin groups (the bv_ILA anatomy): o1 ≡ o2 through GATE
    // CONGRUENCE — both defined as a ∧ b — with NO binary path between
    // them.  These exercise the augmented-class path that plain
    // equivalence pairs never touch (the classes exist only through
    // `augment_big_with_gate_congruence`).
    let gates = 1 + (rand(seed) as usize) % 3;
    for _ in 0..gates {
        let a = 1 + (rand(seed) as usize) % nvars;
        let b = 1 + (rand(seed) as usize) % nvars;
        let o1 = 1 + (rand(seed) as usize) % nvars;
        let o2 = 1 + (rand(seed) as usize) % nvars;
        if a == b || o1 == o2 || o1 == a || o1 == b || o2 == a || o2 == b {
            continue;
        }
        // o ↔ a∧b, both twins: (¬a ∨ ¬b ∨ o), (¬o ∨ a), (¬o ∨ b).
        for &o in &[o1, o2] {
            f.push(vec![nlit(a, false), nlit(b, false), nlit(o, true)]);
            f.push(vec![nlit(o, false), nlit(a, true)]);
            f.push(vec![nlit(o, false), nlit(b, true)]);
        }
    }
    // Random fillers.
    while f.len() < nclauses {
        let len = 2 + (rand(seed) as usize) % 3;
        let len = len.min(nvars);
        let mut c: Vec<i32> = Vec::new();
        let mut guard = 0;
        while c.len() < len && guard < 4 * len {
            guard += 1;
            let v = 1 + (rand(seed) as usize) % nvars;
            let l = nlit(v, rand(seed) & 1 == 0);
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
        enable_equiv_substitution: true,
        enable_gate_congruence: true,
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
        let nvars = 8 + (rand(&mut seed) as usize) % 24;
        let nclauses = 24 + (rand(&mut seed) as usize) % 120;
        let f = gen_formula(&mut seed, nvars, nclauses);
        let cnf = to_cnf(nvars, &f);
        let (r_off, _) = solve(&cnf);
        let (r_on, m_on) = solve(&cnf);
        let agree = matches!(
            (r_off, r_on),
            (SolverResult::Sat, SolverResult::Sat)
                | (SolverResult::Unsat, SolverResult::Unsat)
                | (SolverResult::Unknown, _)
                | (_, SolverResult::Unknown)
        );
        assert!(
            agree,
            "{label} MISMATCH iter={i} nv={nvars}: {r_off:?} vs {r_on:?}\n{cnf}"
        );
        if matches!(r_on, SolverResult::Sat) {
            sat += 1;
            assert!(
                model_ok(&m_on, &f),
                "{label} INVALID MODEL iter={i} nv={nvars}\n{cnf}"
            );
        }
    }
    println!("{label}: iters={iters} sat={sat} mismatches=0 invalid=0");
}

#[test]
fn gate_subsume_differential_soundness() {
    // Scratch reproducer mode (not landed as-is; used to minimize the
    // counterexample): NIXIE_GS_FILE=<cnf> prints the armed verdict,
    // model, and violated original clauses.
    if let Ok(path) = std::env::var("NIXIE_GS_FILE") {
        if std::env::var("NIXIE_GS_ARM").as_deref() != Ok("0") {
            unsafe { std::env::set_var("NIXIE_GATE_SUBSUME", "1") };
        }
        let cnf = std::fs::read_to_string(&path).expect("read NIXIE_GS_FILE");
        let (r, m) = solve(&cnf);
        println!("verdict={r:?}");
        let model: Vec<String> = m
            .iter()
            .enumerate()
            .map(|(i, &b)| format!("{}={}", i + 1, b))
            .collect();
        println!("model={}", model.join(" "));
        // Re-derive the clause list from the file for violation checks.
        let clauses: Vec<Vec<i32>> = cnf
            .lines()
            .filter(|l| !l.starts_with('p') && !l.starts_with('c'))
            .filter(|l| !l.trim().is_empty())
            .map(|l| {
                l.split_whitespace()
                    .map(|t| t.parse::<i32>().unwrap_or(0))
                    .take_while(|&v| v != 0)
                    .collect()
            })
            .collect();
        let bad: Vec<String> = clauses
            .iter()
            .filter(|c| {
                !c.iter().any(|&v| {
                    let vi = v.unsigned_abs() as usize - 1;
                    m.get(vi).copied() == Some(if v > 0 { 1 } else { 0 })
                })
            })
            .map(|c| format!("{:?}", c))
            .collect();
        println!("violated={} {}", bad.len(), bad.join(" | "));
        return;
    }
    // Process-wide env (nextest runs each test in its own process): this
    // test IS the armed arm.
    unsafe { std::env::set_var("NIXIE_GATE_SUBSUME", "1") };
    differential("gate-subsume", 20_000, 0x6A7E_2021);
}
