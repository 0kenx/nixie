//! Semantic boundary distinctions (production `Boundary`).
//!
//! The answer hinges on exact SMT-LIB `div`/`mod` (Euclidean: remainder
//! always non-negative for positive divisors) — distinctions that a
//! sloppy rewrite, truncation, or C-style semantics would erase.
//!
//! * `identity` (UNSAT): `(div (m*x) m)` vs `(div (m*x + m) m) - 1` are
//!   equal for *all* integers x when m > 0 (exact divisions); asserted
//!   distinct. Verified exhaustively over a range plus large samples.
//! * `needle` (SAT): a chain of exact residues pins x, with ground
//!   div/mod facts (including negative operands) prepended as rewrite
//!   stress; a final disequality is satisfiable at the planted x*.

use crate::{Answer, Instance, InstanceKind, Rng, smt_div, smt_mod};
use std::fmt::Write as _;

pub struct Params {
    pub facts: usize,
}

pub enum Fact {
    /// `(mod a b) = r`
    Mod(i64, i64),
    /// `(div a b) = q`
    Div(i64, i64),
    /// `(mod (* a c) b) = r`
    ModMul(i64, i64, i64),
    /// `(mod (div a b) c) = r`
    Nested(i64, i64, i64),
}

impl Fact {
    fn value(&self) -> i64 {
        match self {
            Fact::Mod(a, b) => smt_mod(*a, *b),
            Fact::Div(a, b) => smt_div(*a, *b),
            Fact::ModMul(a, c, b) => smt_mod(a.checked_mul(*c).unwrap_or(*a), *b),
            Fact::Nested(a, b, c) => smt_mod(smt_div(*a, *b), *c),
        }
    }

    fn emit(&self) -> String {
        match self {
            Fact::Mod(a, b) => format!("(assert (= (mod {a} {b}) {}))", self.value()),
            Fact::Div(a, b) => format!("(assert (= (div {a} {b}) {}))", self.value()),
            Fact::ModMul(a, c, b) => format!("(assert (= (mod (* {a} {c}) {b}) {}))", self.value()),
            Fact::Nested(a, b, c) => {
                format!("(assert (= (mod (div {a} {b}) {c}) {}))", self.value())
            }
        }
    }

    fn describe(&self) -> String {
        format!("{} = {}", self.expr_text(), self.value())
    }

    fn expr_text(&self) -> String {
        match self {
            Fact::Mod(a, b) => format!("(mod {a} {b})"),
            Fact::Div(a, b) => format!("(div {a} {b})"),
            Fact::ModMul(a, c, b) => format!("(mod (* {a} {c}) {b})"),
            Fact::Nested(a, b, c) => format!("(mod (div {a} {b}) {c})"),
        }
    }
}

pub struct Data {
    pub identity_m: i64,
    pub facts: Vec<Fact>,
    pub x_star: i64,
    /// (b, r, q): pins `(mod x b) = r` and `(div x b) = q`.
    pub pins: Vec<(i64, i64, i64)>,
    /// (b3, w): `(mod x b3)` is asserted distinct from w, w != smod(x*, b3).
    pub needle: (i64, i64),
}

impl Data {
    pub fn verify(&self) -> Result<(), String> {
        if self.identity_m <= 0 || self.identity_m % 2 == 0 {
            return Err("boundary: identity modulus must be odd and positive".into());
        }
        // Identity: f(x) = div(m*x, m), g(x) = div(m*x + m, m) - 1.
        let m = self.identity_m;
        let f = |x: i64| -> Option<i64> {
            let p = x.checked_mul(m)?;
            Some(smt_div(p, m))
        };
        let g = |x: i64| -> Option<i64> {
            let p = x.checked_mul(m)?.checked_add(m)?;
            smt_div(p, m).checked_sub(1)
        };
        let mut xs: Vec<i64> = (-2000..=2000).collect();
        xs.extend([i64::MIN / 4, -987654321i64, 123456789i64, i64::MAX / 4]);
        for &x in &xs {
            match (f(x), g(x)) {
                (Some(a), Some(b)) if a == b => {}
                (None, None) => {}
                _ => return Err(format!("boundary: identity fails at x = {x}")),
            }
        }
        // Pins are computed from x*.
        for &(b, r, q) in &self.pins {
            if b < 2 || r != smt_mod(self.x_star, b) || q != smt_div(self.x_star, b) {
                return Err("boundary: pin inconsistent with x*".into());
            }
        }
        let (b3, w) = self.needle;
        if b3 < 2 || w == smt_mod(self.x_star, b3) {
            return Err("boundary: needle not actually distinguishing".into());
        }
        if self.pins.iter().any(|&(b, _, _)| b == b3) {
            return Err("boundary: needle modulus collides with a pin".into());
        }
        Ok(())
    }
}

pub fn build(seed: u64, p: &Params) -> Result<Data, String> {
    let mut rng = Rng::new(seed ^ 0xB0A5_E12A);
    let identity_m = rng.range_i64(3, 997) | 1; // odd
    let mut facts: Vec<Fact> = Vec::new();
    for _ in 0..p.facts {
        let kind = rng.index(4);
        let a = rng.range_i64(-120, 120);
        let b = rng.range_i64(2, 13);
        let c = rng.range_i64(-12, 12);
        let fact = match kind {
            0 => Fact::Mod(a, b),
            1 => Fact::Div(a, b),
            2 => Fact::ModMul(a, c, b),
            _ => Fact::Nested(a, b, rng.range_i64(2, 9)),
        };
        facts.push(fact);
    }
    let x_star = rng.range_i64(-1_000_000_000, 1_000_000_000);
    let mut used = std::collections::BTreeSet::new();
    let mut pins: Vec<(i64, i64, i64)> = Vec::new();
    for _ in 0..3 {
        let b = loop {
            let b = rng.range_i64(2, 97);
            if used.insert(b) {
                break b;
            }
        };
        pins.push((b, smt_mod(x_star, b), smt_div(x_star, b)));
    }
    let b3 = loop {
        let b = rng.range_i64(2, 97);
        if used.insert(b) {
            break b;
        }
    };
    let r3 = smt_mod(x_star, b3);
    let w = (r3 + 1 + rng.index((b3 - 2).max(1) as usize) as i64) % b3;
    let d = Data {
        identity_m,
        facts,
        x_star,
        pins,
        needle: (b3, w),
    };
    d.verify()?;
    Ok(d)
}

pub fn generate(seed: u64, p: &Params, suffix: &str) -> Result<Vec<Instance>, String> {
    let d = build(seed, p)?;
    let mut out = Vec::new();

    // Identity UNSAT (quantifier-free: m is a constant, so (m*x) is linear).
    let m = d.identity_m;
    let mut script =
        ";; boundary identity (UNSAT): div(m*x, m) = div(m*x + m, m) - 1\n(set-logic QF_LIA)\n"
            .to_string();
    let _ = writeln!(script, "(declare-const x Int)");
    let _ = writeln!(
        script,
        "(assert (distinct (div (* x {m}) {m}) (- (div (+ (* x {m}) {m}) {m}) 1)))"
    );
    script.push_str("(check-sat)\n");
    out.push(Instance {
        family: "boundary",
        name: format!("boundary-identity-unsat-s{seed}-{suffix}"),
        logic: "QF_LIA".into(),
        script,
        kind: InstanceKind::Smt2,
        expected: vec![Answer::Unsat],
        witness: None,
        certificate: format!(
            "For all integers x with m = {m} > 0: (m*x) div m = x exactly, and (m*x + m) div m = x + 1 exactly (m divides both), so f = g everywhere. Verified over [-2000, 2000] and large samples in the generator; a truncating or non-Euclidean division semantics would answer sat."
        ),
        tags: vec!["boundary", "div-mod", "euclidean"],
    });

    // Needle SAT with ground facts.
    let mut script =
        ";; boundary needle (SAT): exact residues pin x\n(set-logic QF_LIA)\n".to_string();
    for fact in &d.facts {
        let _ = writeln!(script, "{}", fact.emit());
    }
    let _ = writeln!(script, "(declare-const x Int)");
    for &(b, r, q) in &d.pins {
        let _ = writeln!(script, "(assert (= (mod x {b}) {r}))");
        let _ = writeln!(script, "(assert (= (div x {b}) {q}))");
    }
    let (b3, w) = d.needle;
    let _ = writeln!(script, "(assert (distinct (mod x {b3}) {w}))");
    script.push_str("(check-sat)\n");
    let pin_txt: Vec<String> = d
        .pins
        .iter()
        .map(|(b, _, _)| format!("mod/div x {b}"))
        .collect();
    out.push(Instance {
        family: "boundary",
        name: format!("boundary-needle-sat-s{seed}-{suffix}"),
        logic: "QF_LIA".into(),
        script,
        kind: InstanceKind::Smt2,
        expected: vec![Answer::Sat],
        witness: Some(format!("x = {}", d.x_star)),
        certificate: format!(
            "x* = {} satisfies every pin (mod x* {b3} = {}, which is distinct from w = {w}); all ground facts were computed with exact Euclidean semantics in the generator: {}.",
            d.x_star,
            smt_mod(d.x_star, b3),
            d.facts.iter().map(|f| f.describe()).collect::<Vec<_>>().join("; ")
        ),
        tags: vec!["boundary", "div-mod", "needle"],
    });
    let _ = pin_txt;
    Ok(out)
}
