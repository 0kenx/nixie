//! Differential blast soundness at odd and boundary widths.
//!
//! Every case builds a bit-vector term `T` over **free** variables and
//! derives from it an identity `lhs ≡ rhs` that is valid *by construction*
//! (double negation, concat/extract split, De Morgan, division
//! reconstruction, …).  Two scripts are then solved:
//!
//! * `(assert (not (= lhs rhs)))` → must be **unsat** (the identity holds);
//! * `(assert (= lhs rhs))` → must be **sat** (the same identity,
//!   positively — a blaster that refutes both has a false `unsat`, one
//!   that satisfies both has a false `sat`).
//!
//! Because the inputs are free, the ground constant folder cannot decide
//! the case: the *bit-blaster* has to build the circuits and the SAT core
//! has to prove/refute the equality — this is the layer where the
//! historical wide-width bugs lived (`bv_wide_soundness.rs`) and where the
//! reverted structural-rewriting study left a latent, un-root-caused
//! width-126 interaction (`docs/studies/2026-09-10-bv-structural-rewriting-screen.md`,
//! revival path item 1).  The width pool below is chosen around every
//! limb boundary (63/64/65, 125/126/127) and odd small widths.
//!
//! Deterministic: the RNG is a fixed-seed LCG, so a failure reproduces
//! from the case index printed in the panic message.

use nixie_solver::{Context, SolverResult};

// ======== deterministic RNG ========

/// xorshift64* — small, seedable, no dependencies.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed | 1)
    }
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    /// Uniform-ish pick from `xs`.
    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[(self.next() % xs.len() as u64) as usize]
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

// ======== random term trees ========

/// Widths around every historical danger zone.
const WIDTHS: &[u32] = &[
    1, 2, 3, 5, 9, 16, 17, 31, 32, 33, 63, 64, 65, 96, 125, 126, 127, 128,
];

/// A generated bit-vector term: the SMT-LIB emitter and the identity
/// templates both walk this tree.
enum Term {
    /// Variable index *and its width* (the tree is self-describing; the
    /// generator's registry only supplies the declaration list).
    Var(usize, u32),
    Not(Box<Term>),
    And(Box<Term>, Box<Term>),
    Or(Box<Term>, Box<Term>),
    Xor(Box<Term>, Box<Term>),
    Add(Box<Term>, Box<Term>),
    Sub(Box<Term>, Box<Term>),
    MulConst(Box<Term>, u64),
    ShlConst(Box<Term>, u64),
    Concat(Box<Term>, Box<Term>),
    Extract {
        arg: Box<Term>,
        high: u32,
        low: u32,
    },
}

impl Term {
    fn width(&self) -> u32 {
        match self {
            Term::Var(_, w) => *w,
            Term::Not(a) | Term::MulConst(a, _) | Term::ShlConst(a, _) => a.width(),
            Term::Extract { high, low, .. } => high - low + 1,
            Term::And(a, _)
            | Term::Or(a, _)
            | Term::Xor(a, _)
            | Term::Add(a, _)
            | Term::Sub(a, _) => a.width(),
            Term::Concat(h, l) => h.width() + l.width(),
        }
    }
    fn emit(&self, vars: &[&str], out: &mut String) {
        match self {
            Term::Var(i, _) => out.push_str(vars[*i]),
            Term::Not(a) => {
                out.push_str("(bvnot ");
                a.emit(vars, out);
                out.push(')');
            }
            Term::And(a, b)
            | Term::Or(a, b)
            | Term::Xor(a, b)
            | Term::Add(a, b)
            | Term::Sub(a, b) => {
                let op = match self {
                    Term::And(..) => "bvand",
                    Term::Or(..) => "bvor",
                    Term::Xor(..) => "bvxor",
                    Term::Add(..) => "bvadd",
                    _ => "bvsub",
                };
                out.push('(');
                out.push_str(op);
                out.push(' ');
                a.emit(vars, out);
                out.push(' ');
                b.emit(vars, out);
                out.push(')');
            }
            Term::MulConst(a, c) => {
                let w = a.width();
                out.push_str(&format!("(bvmul (_ bv{c} {w}) "));
                a.emit(vars, out);
                out.push(')');
            }
            Term::ShlConst(a, k) => {
                let w = a.width();
                out.push_str("(bvshl ");
                a.emit(vars, out);
                out.push_str(&format!(" (_ bv{k} {w}))"));
            }
            Term::Concat(h, l) => {
                out.push_str("(concat ");
                h.emit(vars, out);
                out.push(' ');
                l.emit(vars, out);
                out.push(')');
            }
            Term::Extract { arg, high, low } => {
                out.push_str(&format!("((_ extract {high} {low}) "));
                arg.emit(vars, out);
                out.push(')');
            }
        }
    }
}

/// Build a random term of exactly `width` bits, depth-bounded, over `vars`.
///
/// Concat/extract steps deliberately create *mixed* widths underneath a
/// target width — extract-of-concat and concat-of-extract at odd offsets
/// are the shapes the width-126 bug class lived in.
fn gen_term(
    rng: &mut Rng,
    width: u32,
    _vars: &[(String, u32)],
    depth: u32,
    out: &mut Vec<(String, u32)>,
) -> Term {
    // The shared pool the generator draws leaves from: declared vars of the
    // requested width, or freshly minted ones.
    fn leaf(rng: &mut Rng, width: u32, out: &mut Vec<(String, u32)>) -> Term {
        let same: Vec<usize> = out
            .iter()
            .enumerate()
            .filter(|(_, (_, w))| *w == width)
            .map(|(i, _)| i)
            .collect();
        if !same.is_empty() && rng.below(3) > 0 {
            let i = same[rng.below(same.len() as u64) as usize];
            Term::Var(i, width)
        } else {
            let name = format!("v{}", out.len());
            out.push((name.clone(), width));
            Term::Var(out.len() - 1, width)
        }
    }
    if depth == 0 {
        return leaf(rng, width, out);
    }
    match rng.below(11) {
        0 | 1 => Term::Not(Box::new(gen_term(rng, width, _vars, depth - 1, out))),
        2 => Term::And(
            Box::new(gen_term(rng, width, _vars, depth - 1, out)),
            Box::new(gen_term(rng, width, _vars, depth - 1, out)),
        ),
        3 => Term::Or(
            Box::new(gen_term(rng, width, _vars, depth - 1, out)),
            Box::new(gen_term(rng, width, _vars, depth - 1, out)),
        ),
        4 => Term::Xor(
            Box::new(gen_term(rng, width, _vars, depth - 1, out)),
            Box::new(gen_term(rng, width, _vars, depth - 1, out)),
        ),
        5 => Term::Add(
            Box::new(gen_term(rng, width, _vars, depth - 1, out)),
            Box::new(gen_term(rng, width, _vars, depth - 1, out)),
        ),
        6 => Term::Sub(
            Box::new(gen_term(rng, width, _vars, depth - 1, out)),
            Box::new(gen_term(rng, width, _vars, depth - 1, out)),
        ),
        7 => Term::MulConst(
            Box::new(gen_term(rng, width, _vars, depth - 1, out)),
            rng.below(7) + 1,
        ),
        8 => Term::ShlConst(
            Box::new(gen_term(rng, width, _vars, depth - 1, out)),
            rng.below(u64::from(width) + 2),
        ),
        // Extract a wider random term down to `width`.
        9 if width < 128 => {
            let super_w = width + (rng.below(4) as u32) + 1;
            let arg = gen_term(rng, super_w, _vars, depth - 1, out);
            Term::Extract {
                arg: Box::new(arg),
                high: width - 1,
                low: 0,
            }
        }
        // Concat two parts that sum to `width`.
        10 if width >= 2 => {
            let hw = rng.below(u64::from(width - 1)) as u32 + 1;
            let lw = width - hw;
            let h = gen_term(rng, hw, _vars, depth - 1, out);
            let l = gen_term(rng, lw, _vars, depth - 1, out);
            Term::Concat(Box::new(h), Box::new(l))
        }
        _ => leaf(rng, width, out),
    }
}

/// One generated identity: `lhs ≡ rhs` valid by construction, plus the
/// script scaffolding (declared vars) both sides share.
struct IdentityCase {
    /// `(name, width)` of every variable the script must declare.
    decls: Vec<(String, u32)>,
    lhs: String,
    rhs: String,
    /// Short description for the failure message.
    what: &'static str,
}

/// Build one random identity case.
fn gen_case(seed: u64) -> IdentityCase {
    let mut rng = Rng::new(seed);
    let width = *rng.pick(WIDTHS);
    let mut vars: Vec<(String, u32)> = Vec::new();
    let t = gen_term(&mut rng, width, &[], 2, &mut vars);
    // At least one variable (the identity must not be ground, or the
    // constant folder decides it without any blast).
    if vars.is_empty() {
        vars.push(("forced".into(), width));
    }
    let var_refs: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
    let var_syms: Vec<&str> = var_refs.iter().map(String::as_str).collect();

    // Template pick.  Every template is a mathematical identity, valid for
    // all values of the free variables.  Each historical bug class in the
    // blaster has a template aimed at it: signed division (the
    // `(bvsdiv s 0)` bug), wide bignum constants (nlzbs128), extension
    // encoders, associativity at limb boundaries.
    let mut lhs = String::new();
    let mut rhs = String::new();
    let what: &'static str;
    match rng.below(15) {
        // 1. Double negation: `~~T ≡ T`.
        0 => {
            lhs.push_str("(bvnot (bvnot ");
            t.emit(&var_syms, &mut lhs);
            lhs.push_str("))");
            t.emit(&var_syms, &mut rhs);
            what = "double negation";
        }
        // 2. Concat/extract split at a random point.
        1 if width >= 2 => {
            let s = rng.below(u64::from(width - 1)) as u32 + 1;
            t.emit(&var_syms, &mut lhs);
            rhs = format!(
                "(concat ((_ extract {} {}) {}) ((_ extract {} 0) {}))",
                width - 1,
                s,
                lhs,
                s - 1,
                lhs
            );
            what = "concat/extract split";
        }
        // 3. Extract-of-concat at an odd split: the top `aw` bits of
        // `concat(A, B)` (`A` high, `B` low) are exactly `A` —
        // `((_ extract w-1 bw) (concat A B)) ≡ A` for every split.
        2 if width >= 2 => {
            let aw = (rng.below(u64::from(width - 1)) as u32) + 1;
            let bw = width - aw;
            let a_term = gen_term(&mut rng, aw, &[], 1, &mut vars);
            let b_term = gen_term(&mut rng, bw, &[], 1, &mut vars);
            let var_refs2: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
            let var_syms2: Vec<&str> = var_refs2.iter().map(String::as_str).collect();
            let mut ab = String::new();
            let mut bb = String::new();
            a_term.emit(&var_syms2, &mut ab);
            b_term.emit(&var_syms2, &mut bb);
            lhs = format!("((_ extract {} {}) (concat {ab} {bb}))", width - 1, bw);
            rhs = ab;
            what = "extract of concat (top part)";
        }
        // 4. De Morgan.
        3 => {
            let mut inner_a = String::new();
            let mut inner_b = String::new();
            let ta = gen_term(&mut rng, width, &[], 1, &mut vars);
            let tb = gen_term(&mut rng, width, &[], 1, &mut vars);
            let vr: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
            let vs: Vec<&str> = vr.iter().map(String::as_str).collect();
            ta.emit(&vs, &mut inner_a);
            tb.emit(&vs, &mut inner_b);
            lhs = format!("(bvnot (bvand {inner_a} {inner_b}))");
            rhs = format!("(bvor (bvnot {inner_a}) (bvnot {inner_b}))");
            what = "De Morgan";
        }
        // 5. XOR with a constant, twice.
        4 => {
            let c: u64 = rng.below(u64::from(width).saturating_mul(3).max(1)) | 1;
            t.emit(&var_syms, &mut lhs);
            rhs = format!("(bvxor (bvxor {lhs} (_ bv{c} {width})) (_ bv{c} {width}))");
            what = "xor const twice";
        }
        // 6. Add/sub cancel.
        5 => {
            let c = rng.below(1 << 20.min(width));
            t.emit(&var_syms, &mut lhs);
            rhs = format!("(bvsub (bvadd {lhs} (_ bv{c} {width})) (_ bv{c} {width}))");
            what = "add/sub cancel";
        }
        // 7. Division reconstruction with a nonzero odd constant divisor:
        //    (T udiv c) * c + (T urem c) == T.  Division circuits are wide;
        //    keep this template at test-budget widths (the udiv encoding is
        //    width-independent in structure, so small widths cover it).
        _ if width <= 33 => {
            let c = rng.below(15) * 2 + 1; // odd, 1..=29, never zero
            t.emit(&var_syms, &mut lhs);
            rhs = format!(
                "(bvadd (bvmul (bvudiv {lhs} (_ bv{c} {width})) (_ bv{c} {width})) (bvurem {lhs} (_ bv{c} {width})))"
            );
            what = "udiv/urem reconstruction";
        }
        // 8. Signed division reconstruction: `a = (a sdiv c)·c + (a srem c)`
        //    for a nonzero constant divisor (truncation toward zero keeps
        //    the equation exact — this is the template aimed at the
        //    historical `(bvsdiv s 0)` encoding bug class).
        7 if width <= 33 => {
            let c = rng.below(15) * 2 + 1;
            t.emit(&var_syms, &mut lhs);
            rhs = format!(
                "(bvadd (bvmul (bvsdiv {lhs} (_ bv{c} {width})) (_ bv{c} {width})) (bvsrem {lhs} (_ bv{c} {width})))"
            );
            what = "sdiv/srem reconstruction";
        }
        // 9. `bvcomp(T, T) ≡ 1` (width-1 result).
        8 => {
            t.emit(&var_syms, &mut lhs);
            lhs = format!("(bvcomp {lhs} {lhs})");
            rhs = "(_ bv1 1)".to_string();
            what = "bvcomp self";
        }
        // 10. `ite(c, T, T) ≡ T` for a comparison-valued selector.
        9 => {
            let cmp_w = *rng.pick(&[1u32, 2, 5, 17, 33]);
            let ca = gen_term(&mut rng, cmp_w, &[], 1, &mut vars);
            let cb = gen_term(&mut rng, cmp_w, &[], 1, &mut vars);
            let vr: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
            let vs: Vec<&str> = vr.iter().map(String::as_str).collect();
            let mut a = String::new();
            let mut b = String::new();
            ca.emit(&vs, &mut a);
            cb.emit(&vs, &mut b);
            t.emit(&var_syms, &mut rhs);
            lhs = format!("(ite (bvult {a} {b}) {rhs} {rhs})");
            what = "ite same branch";
        }
        // 11. `ite(¬c, X, Y) ≡ ite(c, Y, X)` — selector negation commutes
        //     the branches.
        10 => {
            let cmp_w = *rng.pick(&[1u32, 3, 9, 33]);
            let ca = gen_term(&mut rng, cmp_w, &[], 1, &mut vars);
            let cb = gen_term(&mut rng, cmp_w, &[], 1, &mut vars);
            let x = gen_term(&mut rng, width, &[], 1, &mut vars);
            let y = gen_term(&mut rng, width, &[], 1, &mut vars);
            let vr: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
            let vs: Vec<&str> = vr.iter().map(String::as_str).collect();
            let (mut a, mut b, mut xe, mut ye) =
                (String::new(), String::new(), String::new(), String::new());
            ca.emit(&vs, &mut a);
            cb.emit(&vs, &mut b);
            x.emit(&vs, &mut xe);
            y.emit(&vs, &mut ye);
            lhs = format!("(ite (not (bvult {a} {b})) {xe} {ye})");
            rhs = format!("(ite (bvult {a} {b}) {ye} {xe})");
            what = "ite selector negation";
        }
        // 12. Sign extension identity:
        //     `sign_extend(k, T) ≡ ite(msb(T), zero_ext(T) | HIGHMASK, zero_ext(T))`
        //     — the extension encoders at limb-crossing widths.
        11 if width <= 96 => {
            let k = (rng.below(8) as u32) + 1;
            let wide = width + k;
            t.emit(&var_syms, &mut lhs);
            let mut ze = format!("((_ zero_extend {k}) {lhs})");
            // HIGHMASK: bits width..width+k-1 set at width `wide`.
            let mut mask = num_bigint::BigUint::from(0u8);
            for i in width..wide {
                mask.set_bit(u64::from(i), true);
            }
            lhs = format!("((_ sign_extend {k}) {lhs})");
            let mut ts = String::new();
            t.emit(&var_syms, &mut ts);
            rhs = format!(
                "(ite (= ((_ extract {} {}) {ts}) (_ bv1 1)) (bvor {ze} (_ bv{mask} {wide})) {ze})",
                width - 1,
                width - 1
            );
            ze.clear();
            what = "sign extension";
        }
        // 13. Concat associativity: `(A ++ B) ++ C ≡ A ++ (B ++ C)` — the
        //     seam-splitting encoders.
        12 => {
            let wa = (rng.below(u64::from(width.saturating_sub(2))) as u32).max(1);
            let wb = (rng.below(u64::from(width - wa - 1)) as u32).max(1);
            let wc = width - wa - wb;
            let ta = gen_term(&mut rng, wa, &[], 1, &mut vars);
            let tb = gen_term(&mut rng, wb, &[], 1, &mut vars);
            let tc = gen_term(&mut rng, wc, &[], 1, &mut vars);
            let vr: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
            let vs: Vec<&str> = vr.iter().map(String::as_str).collect();
            let (mut a, mut b, mut c) = (String::new(), String::new(), String::new());
            ta.emit(&vs, &mut a);
            tb.emit(&vs, &mut b);
            tc.emit(&vs, &mut c);
            lhs = format!("(concat (concat {a} {b}) {c})");
            rhs = format!("(concat {a} (concat {b} {c}))");
            what = "concat associativity";
        }
        // 14. Add associativity at limb boundaries:
        //     `(A + B) + C ≡ A + (B + C)` (carry-chain regrouping).
        13 if width <= 33 => {
            let ta = gen_term(&mut rng, width, &[], 1, &mut vars);
            let tb = gen_term(&mut rng, width, &[], 1, &mut vars);
            let tc = gen_term(&mut rng, width, &[], 1, &mut vars);
            let vr: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
            let vs: Vec<&str> = vr.iter().map(String::as_str).collect();
            let (mut a, mut b, mut c) = (String::new(), String::new(), String::new());
            ta.emit(&vs, &mut a);
            tb.emit(&vs, &mut b);
            tc.emit(&vs, &mut c);
            lhs = format!("(bvadd (bvadd {a} {b}) {c})");
            rhs = format!("(bvadd {a} (bvadd {b} {c}))");
            what = "add associativity";
        }
        // 15. Wide-constant XOR: `xor(xor(T, HUGE), HUGE) ≡ T` with HUGE
        //     spanning the top limb (≥ 2^64) — the bignum constant paths.
        14 if width >= 65 => {
            let mut huge = num_bigint::BigUint::from(1u8) << (width - 1);
            huge += num_bigint::BigUint::from(7u8) << 32;
            huge += 3u8;
            t.emit(&var_syms, &mut rhs);
            lhs = format!("(bvxor (bvxor {rhs} (_ bv{huge} {width})) (_ bv{huge} {width}))");
            what = "wide-limb xor";
        }
        // Wide widths keep the expensive division circuit out of the test
        // budget: fall back to the cheapest template.
        _ => {
            lhs.push_str("(bvnot (bvnot ");
            t.emit(&var_syms, &mut lhs);
            lhs.push_str("))");
            t.emit(&var_syms, &mut rhs);
            what = "double negation (wide fallback)";
        }
    }
    IdentityCase {
        decls: vars,
        lhs,
        rhs,
        what,
    }
}

/// Solve one script and return its verdict.
fn verdict(script: &str) -> SolverResult {
    let mut ctx = Context::new();
    let outputs = ctx.execute_script(script).unwrap_or_default();
    for tok in outputs.iter().rev() {
        match tok.trim() {
            "sat" => return SolverResult::Sat,
            "unsat" => return SolverResult::Unsat,
            "unknown" => return SolverResult::Unknown,
            _ => {}
        }
    }
    SolverResult::Unknown
}

/// Build the script for one case with the positive or negated identity.
fn script(case: &IdentityCase, negate: bool) -> String {
    let mut s = String::from("(set-logic QF_BV)\n");
    for (name, w) in &case.decls {
        s.push_str(&format!("(declare-fun {name} () (_ BitVec {w}))\n"));
    }
    let eq = format!("(= {} {})", case.lhs, case.rhs);
    if negate {
        s.push_str(&format!("(assert (not {eq}))\n(check-sat)"));
    } else {
        s.push_str(&format!("(assert {eq})\n(check-sat)"));
    }
    s
}

/// The differential pair over random identities at boundary widths.
#[test]
fn odd_width_identity_pairs_hold() {
    let cases = 150;
    for seed in 1..=cases {
        let case = gen_case(seed * 7919);
        let neg = verdict(&script(&case, true));
        let pos = verdict(&script(&case, false));
        assert_eq!(
            neg,
            SolverResult::Unsat,
            "case {seed} ({}): (not (= lhs rhs)) must be unsat — a sat/unknown here is a false model or missing proof\n{}",
            case.what,
            script(&case, true)
        );
        assert_eq!(
            pos,
            SolverResult::Sat,
            "case {seed} ({}): (= lhs rhs) must be sat — an unsat here is a FALSE UNSAT\n{}",
            case.what,
            script(&case, false)
        );
    }
}

/// Out-of-range bit-vector literals are read modulo `2^width` (z3 parity).
///
/// Found by `odd_width_identity_pairs_hold` (case 51): the live parser path
/// for `(_ bvN W)` interned the raw value, so `(_ bv4 1)` and `(_ bv0 1)`
/// were distinct terms and every value-comparing fold answered `(= 4 0)`
/// false — a **false `sat`** on the negated equality.  The fix normalizes
/// constants to their canonical residue at construction (`mk_bitvec`);
/// these pins hold it in place at the limb-boundary widths.
#[test]
fn out_of_range_bv_literals_reduce_modulo_width() {
    // (n, w) pairs where n can exceed 2^w.
    let cases: &[(u128, u32)] = &[
        (4, 1),                      // 4 mod 2 = 0
        (2, 1),                      // 0
        (3, 1),                      // 1
        (256, 8),                    // 0
        (257, 8),                    // 1
        (1 << 32, 32),               // 0
        ((1 << 32) + 5, 32),         // 5
        ((1u128 << 63) - 1 + 2, 63), // 2^63-1 + 2 -> 1
        (1u128 << 64, 64),           // 0
        ((1u128 << 126) + 7, 126),   // 7
    ];
    for &(n, w) in cases {
        let modulus = 1u128 << w;
        let residue = n % modulus;
        let eq = format!(
            "(set-logic QF_BV)\n(assert (= (_ bv{n} {w}) (_ bv{residue} {w})))\n(check-sat)"
        );
        assert_eq!(
            verdict(&eq),
            SolverResult::Sat,
            "(_ bv{n} {w}) must equal its residue {residue}"
        );
        let neq = format!(
            "(set-logic QF_BV)\n(assert (not (= (_ bv{n} {w}) (_ bv{residue} {w}))))\n(check-sat)"
        );
        assert_eq!(
            verdict(&neq),
            SolverResult::Unsat,
            "not(= (_ bv{n} {w}) {residue}) must be unsat (the case-51 false sat)"
        );
        let diff = (residue + 1) % modulus;
        let dif =
            format!("(set-logic QF_BV)\n(assert (= (_ bv{n} {w}) (_ bv{diff} {w})))\n(check-sat)");
        assert_eq!(
            verdict(&dif),
            SolverResult::Unsat,
            "(_ bv{n} {w}) must NOT equal residue+1 ({diff})"
        );
    }
}
