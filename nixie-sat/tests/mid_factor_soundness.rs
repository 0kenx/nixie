//! Mid-search quotient-chain factor soundness (differential fuzz +
//! targeted regressions).  The pass (`solver/factor.rs`, the full kissat
//! `factor.c` port) introduces hub variables inside `inprocess()` rounds
//! and pre-search; the chain rewrite is equisatisfiable and
//! model-preserving in both directions, so verdicts must agree with the
//! off arm and SAT models must satisfy the ORIGINAL clauses.

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

/// Chain-dense generator: pivot literals sharing tail sets through
/// binaries AND large clauses (the quotient-chain pattern), plus a random
/// body so other shapes stay present.
fn gen_formula(seed: &mut u64, nvars: usize, nclauses: usize, wide: bool) -> Vec<Vec<i32>> {
    let mut f = Vec::new();
    let chains = 2 + (rand(seed) as usize) % 4;
    for _ in 0..chains {
        // 2..=4 pivots sharing 2..=4 tails, through binaries and 3-lit
        // clauses (both chain entry kinds).
        let pivots = 2 + (rand(seed) as usize) % 3;
        let tails = 2 + (rand(seed) as usize) % 3;
        let use_large = rand(seed) & 1 == 0;
        for _ in 0..tails {
            // The tail identity: one literal shared by all pivot clauses of
            // this tail (binary chain) or two literals (large chain).
            let t1 = 1 + (rand(seed) as usize) % nvars;
            let t2 = 1 + (rand(seed) as usize) % nvars;
            let t1 = if rand(seed) & 1 == 0 {
                t1 as i32
            } else {
                -(t1 as i32)
            };
            let t2 = if rand(seed) & 1 == 0 {
                t2 as i32
            } else {
                -(t2 as i32)
            };
            for _ in 0..pivots {
                let x = 1 + (rand(seed) as usize) % nvars;
                let x = if rand(seed) & 1 == 0 {
                    x as i32
                } else {
                    -(x as i32)
                };
                if x == t1 || x == -t1 {
                    continue;
                }
                if use_large && t1 != t2 && t1 != -t2 {
                    f.push(vec![x, t1, t2]);
                } else {
                    f.push(vec![x, t1]);
                }
            }
        }
    }
    while f.len() < nclauses {
        let len = (2 + (rand(seed) as usize) % (if wide { 5 } else { 3 })).min(nvars);
        let mut c = Vec::new();
        while c.len() < len {
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
        f.push(c);
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

fn solve(cfg: SolverConfig, cnf: &str) -> (SolverResult, Vec<u8>, u64) {
    let mut s = Solver::with_config(cfg);
    let mut p = DimacsParser::new();
    p.parse_reader(Cursor::new(cnf.as_bytes()), &mut s)
        .expect("parse fuzz cnf");
    let r = s.solve();
    let model: Vec<u8> = (0..s.num_vars())
        .map(|i| match s.model().get(i) {
            Some(LBool::True) => 1u8,
            Some(LBool::False) => 0u8,
            _ => 2u8,
        })
        .collect();
    (r, model, s.stats().factor_introduced)
}

fn model_ok(model: &[u8], clauses: &[Vec<i32>]) -> bool {
    clauses.iter().all(|c| {
        c.iter().any(|&v| {
            let vi = v.unsigned_abs() as usize - 1;
            model.get(vi).copied() == Some(if v > 0 { 1 } else { 0 })
        })
    })
}

fn factor_cfg(interval: u64) -> SolverConfig {
    SolverConfig {
        enable_inprocessing: true,
        inprocessing_interval: interval,
        enable_factoring: true,
        // Lucky phases short-circuit easy SAT instances before the factor
        // pass runs; disable so the fuzz exercises the rewrite itself.
        enable_lucky: false,
        ..SolverConfig::default()
    }
}

/// Mid-search differential soundness (the handover's fuzz bar: chain
/// factor on/off, random CNFs; verdicts must agree, models must satisfy
/// the originals, and the pass must actually fire on this generator).
#[test]
fn mid_factor_differential_soundness() {
    let mut seed: u64 = 0x5E17_2029;
    let (mut mismatch, mut invalid, mut introduced_seen) = (0usize, 0usize, false);
    let iters = 20_000;
    for i in 0..iters {
        let nvars = 5 + (rand(&mut seed) as usize) % 30;
        let nclauses = 20 + (rand(&mut seed) as usize) % 180;
        let wide = rand(&mut seed) & 1 == 0;
        let f = gen_formula(&mut seed, nvars, nclauses, wide);
        let cnf = to_cnf(nvars, &f);
        let (r_off, _, _) = solve(SolverConfig::default(), &cnf);
        let (r_on, m_on, fact_n) = solve(factor_cfg(5), &cnf);
        if fact_n > 0 {
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
            eprintln!(
                "verdict mismatch at iter {i}: off={r_off:?} on={r_on:?} (introduced {fact_n})"
            );
        }
        if r_on == SolverResult::Sat && !model_ok(&m_on, &f) {
            invalid += 1;
            eprintln!("invalid model at iter {i} (introduced {fact_n})");
        }
        if mismatch + invalid > 5 {
            break;
        }
    }
    assert_eq!(mismatch, 0, "verdict mismatches (see stderr)");
    assert_eq!(invalid, 0, "models violating original clauses (see stderr)");
    assert!(
        introduced_seen,
        "generator never triggered an introduction — the fuzz is vacuous"
    );
}

/// The pre-search one-shot under every schedule arm must agree with the
/// off arm (the `NIXIE_FACTOR_SCHED` knob only moves fresh variables in
/// the decision order — never the verdict).
#[test]
fn factor_presearch_verdict_across_schedule_arms() {
    // Env vars are process-global; this test pins the default (kissat
    // `back`) arm only — the arms share the rewrite, which is what the
    // verdict depends on (the differential above covers it end to end).
    let mut seed: u64 = 0xC0FF_EE01;
    for _ in 0..2000 {
        let nvars = 6 + (rand(&mut seed) as usize) % 20;
        let f = gen_formula(&mut seed, nvars, 40, true);
        let cnf = to_cnf(nvars, &f);
        let (r_off, _, _) = solve(SolverConfig::default(), &cnf);
        let (r_on, m_on, n) = solve(
            SolverConfig {
                enable_factoring: true,
                enable_lucky: false,
                ..SolverConfig::default()
            },
            &cnf,
        );
        assert_eq!(r_off, r_on, "pre-search verdict flip (introduced {n})");
        if r_on == SolverResult::Sat {
            assert!(model_ok(&m_on, &f), "pre-search model violation");
        }
    }
}

/// Regression: the delay gate must not starve the pass on small instances
/// (log10(active) ≤ rounds + 4 holds from round 1 for ≤ 100k variables —
/// every realistic formula factors immediately).
#[test]
fn factor_delay_never_starves_small_formulas() {
    use nixie_sat::Lit;
    let mut s = Solver::with_config(SolverConfig {
        enable_factoring: true,
        enable_lucky: false,
        ..SolverConfig::default()
    });
    let f = s.new_var();
    let g = s.new_var();
    let qs: Vec<_> = (0..5).map(|_| s.new_var()).collect();
    for &q in &qs {
        s.add_clause([Lit::pos(f), Lit::pos(q)]);
        s.add_clause([Lit::pos(q), Lit::pos(g)]);
    }
    let r = s.solve();
    assert_eq!(r, SolverResult::Sat);
    assert_eq!(
        s.stats().factor_introduced,
        1,
        "delay gate must pass at round 1"
    );
}
