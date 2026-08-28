//! Differential fuzz harness for the CDCL NIA search (`nia_cdcl`).
//!
//! Generates random small QF_NIA formulas (linear atoms, products of linear
//! atoms, conjunctions and disjunctions), decides them by brute force over
//! `[-6,6]^3`, and compares against [`oxiz_theories::nia_cdcl::cdcl_nia_search`].
//! A wrong-unsat is a soundness bug (the box is ground truth for in-box
//! witnesses); a verified Sat is its own certificate, so only wrong-unsat
//! fails the run.
//!
//! Usage: `cargo run --release -p oxiz-theories --example fuzz_nia -- <seed>
//! <iterations>`; set `OXIZ_NIA_CDCL_MS` to bound each search (e.g. 120).
//! This harness is what surfaced the Tseitin gate-aliasing wrong-unsat and
//! the simplex frame leak; run it after touching the encoder or the theory
//! loop.
#[cfg(feature = "nlsat")]
use num_bigint::BigInt;
#[cfg(feature = "nlsat")]
use oxiz_core::ast::{TermId, TermManager};

#[cfg(feature = "nlsat")]
fn main() {
    let seed: u64 = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(42);
    let n_iters: usize = std::env::args()
        .nth(2)
        .and_then(|s| s.parse().ok())
        .unwrap_or(2000);
    let mut rng = Rng::new(seed);
    for it in 0..n_iters {
        let mut m = TermManager::new();
        let vars: Vec<TermId> = (0..3)
            .map(|i| m.mk_var(&format!("v{}", i), m.sorts.int_sort))
            .collect();
        let mut conjuncts: Vec<TermId> = Vec::new();
        for _ in 0..4 {
            let t = if rng.next() & 1 == 0 {
                random_atom(&mut m, &vars, &mut rng)
            } else {
                let a = random_atom(&mut m, &vars, &mut rng);
                let b = random_atom(&mut m, &vars, &mut rng);
                m.mk_or([a, b])
            };
            conjuncts.push(t);
        }
        let goal = m.mk_and(conjuncts);
        let expected = brute_force(&mut m, &vars, goal);
        let got = oxiz_theories::nia_cdcl::cdcl_nia_search(&[goal], &[goal], &mut m);
        let got_v = match got {
            Some(oxiz_theories::nlsat::NlDispatchResult::Sat(_)) => Some(true),
            Some(oxiz_theories::nlsat::NlDispatchResult::Unsat) => Some(false),
            None => None,
        };
        if got_v == Some(false) && expected {
            eprintln!("WRONG-UNSAT iter={}", it);
            print_formula(goal, &m);
            return;
        }
        if got_v.is_none() {
            // Misses are budget artifacts (OXIZ_NIA_CDCL_MS); only wrong
            // verdicts fail the run.
            let _ = expected;
        }
    }
    println!("all {} iterations sound (misses are budget-bound)", n_iters);
}

#[cfg(feature = "nlsat")]
struct Rng(u64);
#[cfg(feature = "nlsat")]
impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed | 1)
    }
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

#[cfg(feature = "nlsat")]
fn rand_lin(m: &mut TermManager, vars: &[TermId], rng: &mut Rng) -> TermId {
    let build = |m: &mut TermManager, rng: &mut Rng| -> TermId {
        let mut parts = vec![m.mk_int((rng.below(7) as i64) - 3)];
        for &v in vars {
            if rng.below(3) > 0 {
                let c = (rng.below(5) as i64) - 2;
                if c == 1 {
                    parts.push(v);
                } else if c != 0 {
                    let ct = m.mk_int(c);
                    parts.push(m.mk_mul([ct, v]));
                }
            }
        }
        m.mk_add(parts)
    };
    let a = build(m, rng);
    if rng.below(4) == 0 {
        let b = build(m, rng);
        m.mk_mul([a, b])
    } else {
        a
    }
}

#[cfg(feature = "nlsat")]
fn random_atom(m: &mut TermManager, vars: &[TermId], rng: &mut Rng) -> TermId {
    let l = rand_lin(m, vars, rng);
    let r = m.mk_int((rng.below(5) as i64) - 2);
    match rng.below(5) {
        0 => m.mk_eq(l, r),
        1 => m.mk_le(l, r),
        2 => m.mk_lt(l, r),
        3 => m.mk_ge(l, r),
        _ => m.mk_gt(l, r),
    }
}

#[cfg(feature = "nlsat")]
fn brute_force(m: &mut TermManager, vars: &[TermId], goal: TermId) -> bool {
    for a in -6..=6 {
        for b in -6..=6 {
            for c in -6..=6 {
                let mut env = std::collections::HashMap::new();
                env.insert(vars[0], BigInt::from(a));
                env.insert(vars[1], BigInt::from(b));
                env.insert(vars[2], BigInt::from(c));
                if oxiz_theories::ania_ground::eval_assertions_true(&[goal], m, &env) {
                    return true;
                }
            }
        }
    }
    false
}

#[cfg(feature = "nlsat")]
fn print_formula(t: TermId, m: &TermManager) {
    fn go(t: TermId, m: &TermManager, out: &mut String) {
        use oxiz_core::ast::TermKind;
        let Some(n) = m.get(t) else { return };
        let join = |xs: &[TermId], out: &mut String, op: &str| {
            out.push_str(op);
            out.push(' ');
            for (i, &x) in xs.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                go(x, m, out);
            }
            out.push(')');
        };
        match &n.kind {
            TermKind::Var(s) => out.push_str(m.resolve_str(*s)),
            TermKind::IntConst(k) => out.push_str(&k.to_string()),
            TermKind::Add(xs) => join(xs, out, "(+"),
            TermKind::Mul(xs) => join(xs, out, "(*"),
            TermKind::Eq(a, b) => {
                out.push_str("(= ");
                go(*a, m, out);
                out.push(' ');
                go(*b, m, out);
                out.push(')');
            }
            TermKind::Le(a, b) => {
                out.push_str("(<= ");
                go(*a, m, out);
                out.push(' ');
                go(*b, m, out);
                out.push(')');
            }
            TermKind::Lt(a, b) => {
                out.push_str("(< ");
                go(*a, m, out);
                out.push(' ');
                go(*b, m, out);
                out.push(')');
            }
            TermKind::Ge(a, b) => {
                out.push_str("(>= ");
                go(*a, m, out);
                out.push(' ');
                go(*b, m, out);
                out.push(')');
            }
            TermKind::Gt(a, b) => {
                out.push_str("(> ");
                go(*a, m, out);
                out.push(' ');
                go(*b, m, out);
                out.push(')');
            }
            TermKind::And(xs) => join(xs, out, "(and"),
            TermKind::Or(xs) => join(xs, out, "(or"),
            TermKind::Neg(a) => {
                out.push_str("(- ");
                go(*a, m, out);
                out.push(')');
            }
            k => out.push_str(&format!("<{:?}>", std::mem::discriminant(k))),
        }
    }
    let mut s = String::new();
    go(t, m, &mut s);
    println!("{}", s);
}

#[cfg(not(feature = "nlsat"))]
fn main() {
    eprintln!("fuzz_nia requires the nlsat feature");
}
