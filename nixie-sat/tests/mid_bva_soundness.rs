//! Mid-search structured BVA soundness (differential fuzz + targeted
//! regressions).  The pass (`solver/bva.rs`, `enable_mid_bva`) introduces
//! aux vars inside `inprocess()` rounds; the encoding is
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

/// Spine-pool generator (same shape as `sbva_soundness.rs`): makes
/// mergeable groups dense; the random tail keeps other shapes present.
fn gen_formula(seed: &mut u64, nvars: usize, nclauses: usize, wide: bool) -> Vec<Vec<i32>> {
    let mut f = Vec::new();
    // Spines: k clauses sharing a common G.
    let spines = 2 + (rand(seed) as usize) % 4;
    for _ in 0..spines {
        let glen = 2 + (rand(seed) as usize) % 3;
        let g: Vec<i32> = (0..glen)
            .map(|_| {
                let v = 1 + (rand(seed) as usize) % nvars;
                if rand(seed) & 1 == 0 {
                    v as i32
                } else {
                    -(v as i32)
                }
            })
            .collect();
        let k = 2 + (rand(seed) as usize) % 4;
        for _ in 0..k {
            let mut c = g.clone();
            let extra = 1 + (rand(seed) as usize) % (if wide { 4 } else { 2 });
            for _ in 0..extra {
                let v = 1 + (rand(seed) as usize) % nvars;
                let l = if rand(seed) & 1 == 0 {
                    v as i32
                } else {
                    -(v as i32)
                };
                if !c.contains(&l) {
                    c.push(l);
                }
            }
            f.push(c);
        }
    }
    while f.len() < nclauses {
        // Capacity note: a tautology-free clause over `nvars` variables
        // holds at most `nvars` literals (one polarity per variable) —
        // clamp the target length or the rejection loop below never
        // terminates for `len > nvars` (the original generator bug).
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

fn solve(cfg: SolverConfig, cnf: &str) -> (SolverResult, Vec<u8>, usize, u64) {
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
    (r, model, s.num_vars(), s.stats().bva_introduced)
}

fn model_ok(model: &[u8], clauses: &[Vec<i32>]) -> bool {
    clauses.iter().all(|c| {
        c.iter().any(|&v| {
            let vi = v.unsigned_abs() as usize - 1;
            model.get(vi).copied() == Some(if v > 0 { 1 } else { 0 })
        })
    })
}

fn mid_cfg(interval: u64, null: bool) -> SolverConfig {
    SolverConfig {
        enable_inprocessing: true,
        inprocessing_interval: interval,
        enable_mid_bva: true,
        mid_bva_null: null,
        ..SolverConfig::default()
    }
}

fn gate_cfg(interval: u64, null: bool) -> SolverConfig {
    SolverConfig {
        enable_inprocessing: true,
        inprocessing_interval: interval,
        enable_mid_andgate: true,
        mid_andgate_null: null,
        ..SolverConfig::default()
    }
}

/// Hub generator: binaries sharing a common tail literal — the AND-gate
/// pattern — plus the spine/random body.
fn gen_hub_formula(seed: &mut u64, nvars: usize) -> Vec<Vec<i32>> {
    let mut f = Vec::new();
    let hubs = 2 + (rand(seed) as usize) % 3;
    for _ in 0..hubs {
        let q = 1 + (rand(seed) as usize) % nvars;
        let partners = 2 + (rand(seed) as usize) % 5;
        for _ in 0..partners {
            let x = 1 + (rand(seed) as usize) % nvars;
            let q32 = q as i32;
            let x32 = x as i32;
            let ql = if rand(seed) & 1 == 0 { q32 } else { -q32 };
            let xl = if rand(seed) & 1 == 0 { x32 } else { -x32 };
            if ql != xl && ql != -xl {
                f.push(vec![ql, xl]);
            }
        }
    }
    let extra = 40 + (rand(seed) as usize) % 160;
    for _ in 0..extra {
        let len = 2 + (rand(seed) as usize) % 3;
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

/// AND-gate factoring differential soundness: hub-dense formulas force
/// introductions mid-search; verdicts must agree with the off arm and SAT
/// models must satisfy the ORIGINAL clauses (the rewrite is
/// model-preserving downward — see `solver/bva.rs`).
#[test]
fn mid_andgate_differential_soundness() {
    let mut seed: u64 = 0xB4A1_2029;
    let (mut mismatch, mut invalid, mut introduced_seen) = (0usize, 0usize, false);
    let iters = 20_000;
    for i in 0..iters {
        let nvars = 5 + (rand(&mut seed) as usize) % 30;
        let f = gen_hub_formula(&mut seed, nvars);
        let cnf = to_cnf(nvars, &f);
        let (r_off, _, _, _) = solve(SolverConfig::default(), &cnf);
        let (r_on, m_on, _, bva_n) = solve(gate_cfg(5, false), &cnf);
        if bva_n > 0 {
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
                eprintln!("GATE MISMATCH iter={i} nv={nvars}: off={r_off:?} on={r_on:?}");
            }
            continue;
        }
        if matches!(r_on, SolverResult::Sat) && !model_ok(&m_on, &f) {
            invalid += 1;
            if invalid <= 3 {
                eprintln!("GATE INVALID MODEL iter={i} nv={nvars}");
            }
        }
    }
    println!(
        "gate iters={iters} mismatches={mismatch} invalid_models={invalid} introductions_occurred={introduced_seen}"
    );
    assert_eq!(mismatch, 0);
    assert_eq!(invalid, 0);
    assert!(
        introduced_seen,
        "hub generator never triggered an introduction"
    );
}

/// The AND-gate null arm (scrambled group ranking) stays sound.
#[test]
fn mid_andgate_null_arm_soundness() {
    let mut seed: u64 = 0xB4A1_202A;
    let (mut mismatch, mut invalid) = (0usize, 0usize);
    let iters = 8_000;
    for i in 0..iters {
        let nvars = 5 + (rand(&mut seed) as usize) % 30;
        let f = gen_hub_formula(&mut seed, nvars);
        let cnf = to_cnf(nvars, &f);
        let (r_off, _, _, _) = solve(SolverConfig::default(), &cnf);
        let (r_null, m_null, _, _) = solve(gate_cfg(5, true), &cnf);
        let agree = matches!(
            (r_off, r_null),
            (SolverResult::Sat, SolverResult::Sat)
                | (SolverResult::Unsat, SolverResult::Unsat)
                | (SolverResult::Unknown, _)
                | (_, SolverResult::Unknown)
        );
        if !agree {
            mismatch += 1;
            if mismatch <= 3 {
                eprintln!("GATE NULL MISMATCH iter={i} nv={nvars}: off={r_off:?} null={r_null:?}");
            }
            continue;
        }
        if matches!(r_null, SolverResult::Sat) && !model_ok(&m_null, &f) {
            invalid += 1;
        }
    }
    println!("gate-null iters={iters} mismatches={mismatch} invalid_models={invalid}");
    assert_eq!(mismatch, 0);
    assert_eq!(invalid, 0);
}

/// Pigeonhole under the AND-gate arm at interval 1 stays Unsat (the pass
/// fires every conflict over a binary-dense refutation).
#[test]
fn pigeonhole_mid_andgate_interval_1_stays_unsat() {
    let holes = 4;
    let pigeons = 5;
    let mut clauses = Vec::new();
    for p in 1..=pigeons {
        let c: Vec<i32> = (1..=holes).map(|h| ((p - 1) * holes + h) as i32).collect();
        clauses.push(c);
    }
    for p in 1..=pigeons {
        for h in 1..=holes {
            for h2 in (h + 1)..=holes {
                clauses.push(vec![
                    -(((p - 1) * holes + h) as i32),
                    -(((p - 1) * holes + h2) as i32),
                ]);
            }
        }
    }
    for h in 1..=holes {
        for p in 1..=pigeons {
            for p2 in (p + 1)..=pigeons {
                clauses.push(vec![
                    -(((p - 1) * holes + h) as i32),
                    -(((p2 - 1) * holes + h) as i32),
                ]);
            }
        }
    }
    let cnf = to_cnf(pigeons * holes, &clauses);
    let (r_off, _, _, _) = solve(SolverConfig::default(), &cnf);
    let (r_on, _, _, _) = solve(gate_cfg(1, false), &cnf);
    assert_eq!(r_off, SolverResult::Unsat);
    assert_eq!(r_on, SolverResult::Unsat);
}

#[test]
fn mid_bva_differential_soundness() {
    // Frequent rounds (interval 10) force the pass to fire mid-search
    // repeatedly, including on formulas whose level-0 trail carries
    // original-clause reasons (the reason-skip path).
    let mut seed: u64 = 0xB4A1_2027;
    let (mut mismatch, mut invalid, mut sat, mut introduced_seen) = (0usize, 0usize, 0usize, false);
    let iters = 30_000;
    for i in 0..iters {
        let nvars = 5 + (rand(&mut seed) as usize) % 40;
        let nclauses = 8 + (rand(&mut seed) as usize) % 200;
        let wide = rand(&mut seed).is_multiple_of(2);
        let f = gen_formula(&mut seed, nvars, nclauses, wide);
        let cnf = to_cnf(nvars, &f);
        let (r_off, _, _, _) = solve(SolverConfig::default(), &cnf);
        let (r_on, m_on, vars_on, bva_n) = solve(mid_cfg(5, false), &cnf);
        if vars_on > nvars || bva_n > 0 {
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
            // Model must satisfy the ORIGINAL clauses (model-preservation
            // of the encoding; introduced vars may take any value).
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
    assert!(introduced_seen, "generator never triggered an introduction");
}

#[test]
fn mid_bva_null_arm_soundness() {
    // The matched null introduces the same shapes with scrambled ranking;
    // soundness must not depend on the rank's semantic content.
    let mut seed: u64 = 0xB4A1_2028;
    let (mut mismatch, mut invalid) = (0usize, 0usize);
    let iters = 10_000;
    for i in 0..iters {
        let nvars = 5 + (rand(&mut seed) as usize) % 40;
        let nclauses = 8 + (rand(&mut seed) as usize) % 200;
        let wide = rand(&mut seed).is_multiple_of(2);
        let f = gen_formula(&mut seed, nvars, nclauses, wide);
        let cnf = to_cnf(nvars, &f);
        let (r_off, _, _, _) = solve(SolverConfig::default(), &cnf);
        let (r_null, m_null, _, _) = solve(mid_cfg(5, true), &cnf);
        let agree = matches!(
            (r_off, r_null),
            (SolverResult::Sat, SolverResult::Sat)
                | (SolverResult::Unsat, SolverResult::Unsat)
                | (SolverResult::Unknown, _)
                | (_, SolverResult::Unknown)
        );
        if !agree {
            mismatch += 1;
            if mismatch <= 3 {
                eprintln!("NULL MISMATCH iter={i} nv={nvars}: off={r_off:?} null={r_null:?}");
            }
            continue;
        }
        if matches!(r_null, SolverResult::Sat) && !model_ok(&m_null, &f) {
            invalid += 1;
        }
    }
    println!("null-arm iters={iters} mismatches={mismatch} invalid_models={invalid}");
    assert_eq!(mismatch, 0);
    assert_eq!(invalid, 0);
}

/// The encoding's level-0-units path: an introduced `(G ∨ t)` whose `G` is
/// fully false at level 0 must force `t` and then each `U_i`, exactly as
/// the retired originals did — and a formula that the originals falsify at
/// level 0 must answer Unsat (not Sat) with the pass on.  Group shape:
/// k = 4 clauses over G = {a, b} (saving = (4−1)·2 − 5 = 1 > 0).
#[test]
fn mid_bva_falsified_group_stays_unsat() {
    let cnf = "p cnf 6 10\
         \n1 2 3 0\n1 2 4 0\n1 2 5 0\n1 2 6 0\
         \n-3 0\n-4 0\n-5 0\n-6 0\n-1 0\n-2 0\n";
    let (r_off, _, _, _) = solve(SolverConfig::default(), cnf);
    let (r_on, _, _, _n) = solve(mid_cfg(2, false), cnf);
    assert_eq!(r_off, SolverResult::Unsat);
    // (Introductions are not guaranteed here: the pre-search simplifier
    // shrinks the group to binaries before the first round fires; the
    // differential fuzz below asserts introductions occur overall.)
    assert_eq!(r_on, SolverResult::Unsat, "mid-BVA must not flip Unsat→Sat");
}

/// Pigeonhole with a tiny interval and mid-BVA on must stay Unsat — the
/// pass runs every conflict and must never break the refutation
/// (companion to `pigeonhole_inprocessing_interval_1_stays_unsat`).
/// Pigeons > holes is the unsatisfiable direction.
#[test]
fn pigeonhole_mid_bva_interval_1_stays_unsat() {
    let holes = 4;
    let pigeons = 5;
    let mut clauses = Vec::new();
    for p in 1..=pigeons {
        let c: Vec<i32> = (1..=holes).map(|h| ((p - 1) * holes + h) as i32).collect();
        clauses.push(c);
    }
    for p in 1..=pigeons {
        for h in 1..=holes {
            for h2 in (h + 1)..=holes {
                clauses.push(vec![
                    -(((p - 1) * holes + h) as i32),
                    -(((p - 1) * holes + h2) as i32),
                ]);
            }
        }
    }
    for h in 1..=holes {
        for p in 1..=pigeons {
            for p2 in (p + 1)..=pigeons {
                clauses.push(vec![
                    -(((p - 1) * holes + h) as i32),
                    -(((p2 - 1) * holes + h) as i32),
                ]);
            }
        }
    }
    let cnf = to_cnf(pigeons * holes, &clauses);
    let (r_off, _, _, _) = solve(SolverConfig::default(), &cnf);
    let (r_on, _, _, _) = solve(mid_cfg(1, false), &cnf);
    assert_eq!(r_off, SolverResult::Unsat);
    assert_eq!(r_on, SolverResult::Unsat);
}

/// Introductions must survive `reset()`/re-solve cycles without corrupting
/// a second solve on the same solver instance.
#[test]
fn mid_bva_reset_and_resolve() {
    let f = gen_formula(&mut 0x5EED_0001, 12, 40, true);
    let cnf = to_cnf(12, &f);
    let mut s = Solver::with_config(mid_cfg(2, false));
    let mut p = DimacsParser::new();
    p.parse_reader(Cursor::new(cnf.as_bytes()), &mut s)
        .expect("parse fuzz cnf");
    let r1 = s.solve();
    s.reset();
    let mut p2 = DimacsParser::new();
    p2.parse_reader(Cursor::new(cnf.as_bytes()), &mut s)
        .unwrap();
    let r2 = s.solve();
    assert_eq!(r1, r2, "re-solve after mid-BVA must agree");
}

/// Pair-mode AND-gate (NIXIE_ANDGATE=2): one hub per pivot pair across all
/// shared tails.  Soundness must not depend on the mode; the hub generator
/// produces the pivot-pair pattern densely (several tails shared between
/// pairs of hub literals).
#[test]
fn mid_andgate_pair_mode_soundness() {
    // Construct config directly: pair mode is env-selected at the pass, so
    // this test sets it via the same env read (one process per test under
    // nextest; safe there, and `cargo test` runs it before any parallel
    // solver test can race the OnceLock in this binary).
    // Safety: single-threaded test start; nextest runs each test in its
    // own process, and this is the first statement before any solver runs.
    unsafe { std::env::set_var("NIXIE_ANDGATE", "2") };
    let mut seed: u64 = 0xB4A1_202B;
    let (mut mismatch, mut invalid, mut introduced_seen) = (0usize, 0usize, false);
    let iters = 15_000;
    for i in 0..iters {
        let nvars = 6 + (rand(&mut seed) as usize) % 28;
        let mut f = Vec::new();
        // Pivot-pair spines: pick x1,x2 and 2-5 shared tails q.
        let spines = 1 + (rand(&mut seed) as usize) % 3;
        for _ in 0..spines {
            let x1 = 1 + (rand(&mut seed) as usize) % nvars;
            let x2 = 1 + (rand(&mut seed) as usize) % nvars;
            if x1 == x2 {
                continue;
            }
            let ntails = 2 + (rand(&mut seed) as usize) % 4;
            for _ in 0..ntails {
                let q = 1 + (rand(&mut seed) as usize) % nvars;
                let mut mk = |v: usize| -> i32 {
                    let l = v as i32;
                    if rand(&mut seed) & 1 == 0 { l } else { -l }
                };
                let (a, b, c) = (mk(x1), mk(x2), mk(q));
                if a != c && a != -c {
                    f.push(vec![a, c]);
                }
                if b != c && b != -c {
                    f.push(vec![b, c]);
                }
            }
        }
        let extra = 30 + (rand(&mut seed) as usize) % 120;
        for _ in 0..extra {
            let len = 2 + (rand(&mut seed) as usize) % 3;
            let mut c: Vec<i32> = Vec::new();
            let mut guard = 0;
            while c.len() < len && guard < 4 * len {
                guard += 1;
                let v = 1 + (rand(&mut seed) as usize) % nvars;
                let l = if rand(&mut seed) & 1 == 0 {
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
        let cnf = to_cnf(nvars, &f);
        let (r_off, _, _, _) = solve(SolverConfig::default(), &cnf);
        let (r_on, m_on, _, bva_n) = solve(gate_cfg(5, false), &cnf);
        if bva_n > 0 {
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
                eprintln!("PAIR MISMATCH iter={i} nv={nvars}: off={r_off:?} on={r_on:?}");
            }
            continue;
        }
        if matches!(r_on, SolverResult::Sat) && !model_ok(&m_on, &f) {
            invalid += 1;
            if invalid <= 3 {
                eprintln!("PAIR INVALID MODEL iter={i} nv={nvars}");
            }
        }
    }
    unsafe { std::env::remove_var("NIXIE_ANDGATE") };
    println!(
        "pair iters={iters} mismatches={mismatch} invalid_models={invalid} intros={introduced_seen}"
    );
    assert_eq!(mismatch, 0);
    assert_eq!(invalid, 0);
    assert!(
        introduced_seen,
        "generator never triggered a pair introduction"
    );
}
