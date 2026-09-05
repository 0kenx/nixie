//! Abstraction-gap obstruction (production `AbstractionGap`).
//!
//! A square linear system `A x = b` with `0 <= x <= 1` that is
//! * rationally feasible (x = 1/2 works, by construction), but
//! * integer-infeasible, certified by an integer combination `u` of the
//!   rows such that every entry of `u^T (2A)` is divisible by `g` while
//!   `u^T (2b)` is not — so `u^T (2A) x = u^T (2b)` has no integer
//!   solution.
//!
//! The conflict depends on integrality: ordinary rational infeasibility
//! cannot explain it. Constructed by choosing a modulus `m`, a weight
//! vector `u`, and columns with `u^T col ≡ 0 (mod m)`; the obstruction is
//! `m * (odd/2)` in `u^T b`, invisible to any LP relaxation.
//!
//! `scale_log10` multiplies all emitted coefficients/rows by `10^k`
//! (exact: same solution set over Q and over Z) — numeral stress.
//! A QF_LRA twin over the *same* system is SAT with witness x = 1/2,
//! forming a differential pair that pins down integrality handling.

use crate::{Answer, Instance, InstanceKind, Rng};
use std::fmt::Write as _;

pub struct Params {
    pub vars: usize,
    pub scale_log10: u32,
}

pub struct Data {
    pub n: usize,
    /// Modulus used during construction (informative).
    pub m: i64,
    /// Row-combination weights (the certificate kernel).
    pub u: Vec<i64>,
    /// Emitted integer matrix `2*M*a` (i128: coefficients survive scaling).
    pub a2: Vec<Vec<i128>>,
    /// Emitted rhs `M*rowsum`.
    pub rhs2: Vec<i128>,
}

fn gcd_i128(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

impl Data {
    pub fn verify(&self) -> Result<(), String> {
        let n = self.n;
        if self.u.len() != n || self.a2.len() != n || self.rhs2.len() != n {
            return Err("gap: shape mismatch".into());
        }
        for row in &self.a2 {
            if row.len() != n {
                return Err("gap: row width mismatch".into());
            }
        }
        // 1. Rational feasibility: x = 1/2 satisfies every row, i.e.
        //    sum_c a2[r][c] == 2 * rhs2[r].
        for r in 0..n {
            let s: i128 = self.a2[r].iter().sum();
            if s != 2 * self.rhs2[r] {
                return Err(format!("gap: row {r} not satisfied by x = 1/2"));
            }
        }
        // 2. Every row has a nonzero coefficient (else it is degenerate).
        for r in 0..n {
            if self.a2[r].iter().all(|&v| v == 0) {
                return Err(format!("gap: row {r} is all zeros"));
            }
        }
        // 3. Integrality obstruction: g = gcd of the combined row entries
        //    must not divide the combined rhs.
        let mut g: i128 = 0;
        for c in 0..n {
            let mut v: i128 = 0;
            for r in 0..n {
                v += self.u[r] as i128 * self.a2[r][c];
            }
            g = gcd_i128(g, v);
        }
        if g == 0 {
            return Err("gap: degenerate combination (all zero)".into());
        }
        let mut rr: i128 = 0;
        for r in 0..n {
            rr += self.u[r] as i128 * self.rhs2[r];
        }
        if rr % g == 0 {
            return Err("gap: obstruction vanished (rhs divisible by gcd)".into());
        }
        Ok(())
    }
}

pub fn build(seed: u64, p: &Params) -> Result<Data, String> {
    if p.vars < 2 {
        return Err("gap: need >= 2 variables".into());
    }
    if p.scale_log10 > 12 {
        return Err("gap: scale_log10 too large".into());
    }
    let scale = 10i128.pow(p.scale_log10);
    let mut last_err = String::new();
    for attempt in 0..64u64 {
        let mut rng = Rng::new(seed.wrapping_add(attempt.wrapping_mul(0x9E37)));
        let n = p.vars;
        let m = rng.range_i64(3, 13);
        let mut u = vec![1i64; n];
        for r in 1..n {
            u[r] = rng.range_i64(1, m); // nonzero mod m
        }
        // a[r][c] for r >= 1 random; a[0][c] chosen so u . col ≡ 0 (mod m).
        let mut a: Vec<Vec<i64>> = vec![vec![0i64; n]; n];
        for c in 0..n {
            for r in 1..n {
                a[r][c] = rng.range_i64(-3, 3);
            }
            let mut s: i64 = 0;
            for r in 1..n {
                s += u[r] * a[r][c];
            }
            let mut a0 = (-s).rem_euclid(m);
            if a0 > m / 2 {
                a0 -= m;
            }
            a[0][c] = a0;
        }
        // Obstruction: sum_c w_c must be odd, w_c = (u . col_c) / m.
        // Adding m to a[0][0] adds u[0]*m/m = 1 to w_0, flipping parity.
        let col: i64 = (0..n).map(|r| u[r] * a[r][0]).sum();
        if col % m != 0 {
            last_err = format!("gap: construction bug, u.col % m = {}", col % m);
            continue;
        }
        let wsum = (0..n)
            .map(|c| (0..n).map(|r| u[r] * a[r][c]).sum::<i64>() / m)
            .sum::<i64>();
        if wsum % 2 == 0 {
            a[0][0] += m;
        }
        let mut a2: Vec<Vec<i128>> = vec![vec![0i128; n]; n];
        let mut rhs2: Vec<i128> = vec![0i128; n];
        for r in 0..n {
            let rowsum: i64 = (0..n).map(|c| a[r][c]).sum();
            for c in 0..n {
                a2[r][c] = 2 * scale * a[r][c] as i128;
            }
            rhs2[r] = scale * rowsum as i128;
        }
        let d = Data { n, m, u, a2, rhs2 };
        match d.verify() {
            Ok(()) => return Ok(d),
            Err(e) => last_err = e,
        }
    }
    Err(format!(
        "gap: could not build a certified instance: {last_err}"
    ))
}

fn fmt_int(v: i128) -> String {
    format!("{v}")
}

fn fmt_real(v: i128) -> String {
    if v < 0 {
        format!("(- {}.0)", -v)
    } else {
        format!("{v}.0")
    }
}

pub fn generate(seed: u64, p: &Params, suffix: &str) -> Result<Vec<Instance>, String> {
    let d = build(seed, p)?;
    let mut out = Vec::new();

    // Integer system: UNSAT.
    let mut script =
        ";; gap lia (rational-feasible, integer-infeasible)\n(set-logic QF_LIA)\n".to_string();
    for c in 0..d.n {
        let _ = writeln!(script, "(declare-const x{c} Int)");
        let _ = writeln!(script, "(assert (>= x{c} 0))");
        let _ = writeln!(script, "(assert (<= x{c} 1))");
    }
    for r in 0..d.n {
        let mut terms: Vec<String> = Vec::new();
        for c in 0..d.n {
            if d.a2[r][c] != 0 {
                terms.push(format!("(* {} x{c})", fmt_int(d.a2[r][c])));
            }
        }
        let _ = writeln!(
            script,
            "(assert (= (+ {}) {}))",
            terms.join(" "),
            fmt_int(d.rhs2[r])
        );
    }
    script.push_str("(check-sat)\n");
    out.push(Instance {
        family: "gap",
        name: format!("gap-lia-unsat-s{seed}-{suffix}"),
        logic: "QF_LIA".into(),
        script,
        kind: InstanceKind::Smt2,
        expected: vec![Answer::Unsat],
        witness: None,
        certificate: format!(
            "x = 1/2 satisfies every row (rational feasibility verified exactly), but the integer combination u = {:?} of the rows has every entry of u.(2A) divisible by g while u.(2b) is not (verified with i128 arithmetic), so no integer solution exists.",
            d.u
        ),
        tags: vec!["abstraction-gap", "lia", "integrality"],
    });

    // Rational twin: SAT with witness x = 1/2.
    let mut script =
        ";; gap lra twin (rational solution x = 1/2)\n(set-logic QF_LRA)\n".to_string();
    for c in 0..d.n {
        let _ = writeln!(script, "(declare-const x{c} Real)");
        let _ = writeln!(script, "(assert (>= x{c} 0.0))");
        let _ = writeln!(script, "(assert (<= x{c} 1.0))");
    }
    for r in 0..d.n {
        let mut terms: Vec<String> = Vec::new();
        for c in 0..d.n {
            if d.a2[r][c] != 0 {
                terms.push(format!("(* {} x{c})", fmt_real(d.a2[r][c])));
            }
        }
        let _ = writeln!(
            script,
            "(assert (= (+ {}) {}))",
            terms.join(" "),
            fmt_real(d.rhs2[r])
        );
    }
    script.push_str("(check-sat)\n");
    out.push(Instance {
        family: "gap",
        name: format!("gap-lra-sat-s{seed}-{suffix}"),
        logic: "QF_LRA".into(),
        script,
        kind: InstanceKind::Smt2,
        expected: vec![Answer::Sat],
        witness: Some("x_c = 1/2 for every variable".into()),
        certificate:
            "Same system over the reals: x = 1/2 satisfies every row and the bounds (verified exactly in the generator)."
                .into(),
        tags: vec!["abstraction-gap", "lra", "differential-pair"],
    });
    Ok(out)
}
