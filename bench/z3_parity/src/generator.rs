//! Deterministic random SMT-LIB2 script generator for differential testing.
//!
//! Generates small, well-typed scripts for `QF_LIA`, `QF_LRA`, `QF_BV` and
//! `QF_UF` (the four logics required by the differential-testing harness in
//! [`crate::difftest`]) using a seeded PRNG, so that any given `(logic,
//! seed)` pair always reproduces byte-for-byte the same script. No
//! wall-clock time, OS entropy, or other non-deterministic input is ever
//! consulted -- this is what lets a failing case be reproduced later from
//! nothing but its seed.
//!
//! The generated formulas are deliberately restricted to stay inside their
//! advertised logic: `QF_LIA`/`QF_LRA` terms are linear (only
//! constant*expression products, never variable*variable), `QF_BV` uses a
//! single fixed bit-width per script, and `QF_UF` only ever applies the two
//! declared uninterpreted functions to a fixed set of constants of a single
//! uninterpreted sort.

use std::fmt::Write as _;

/// Minimal deterministic PRNG (SplitMix64, Vigna's public-domain
/// construction). A dependency-free implementation is used on purpose: the
/// harness only needs a handful of reproducible pseudo-random choices, and
/// avoiding a `rand` dependency means the generated corpus can never shift
/// underneath us because of an unrelated `rand` version bump.
#[derive(Debug, Clone)]
pub struct Rng {
    state: u64,
}

impl Rng {
    pub fn new(seed: u64) -> Self {
        // Golden-ratio constant avoids the degenerate all-zero state and
        // decorrelates seeds that differ only in a couple of bits.
        Rng {
            state: seed ^ 0x9E37_79B9_7F4A_7C15,
        }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Uniform integer in `[0, bound)`. Panics if `bound == 0`.
    fn next_below(&mut self, bound: u64) -> u64 {
        assert!(bound > 0, "Rng::next_below: bound must be positive");
        self.next_u64() % bound
    }

    /// Uniform `i64` in `[lo, hi_inclusive]`.
    pub fn range_i64(&mut self, lo: i64, hi_inclusive: i64) -> i64 {
        assert!(hi_inclusive >= lo, "Rng::range_i64: empty range");
        let span = (hi_inclusive - lo) as u64 + 1;
        lo + self.next_below(span) as i64
    }

    /// True with probability `numerator / denominator`.
    pub fn chance(&mut self, numerator: u64, denominator: u64) -> bool {
        self.next_below(denominator) < numerator
    }

    /// Uniform index into `[0, len)`. Panics if `len == 0`.
    pub fn index(&mut self, len: usize) -> usize {
        self.next_below(len as u64) as usize
    }
}

/// The logics the differential generator supports.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Logic {
    QfLia,
    QfLra,
    QfBv,
    QfUf,
}

impl Logic {
    /// SMT-LIB `set-logic` name.
    pub fn name(self) -> &'static str {
        match self {
            Logic::QfLia => "QF_LIA",
            Logic::QfLra => "QF_LRA",
            Logic::QfBv => "QF_BV",
            Logic::QfUf => "QF_UF",
        }
    }

    /// All logics currently wired into the generator, in a fixed order so
    /// callers can derive per-logic seeds deterministically from an index.
    pub const ALL: [Logic; 4] = [Logic::QfLia, Logic::QfLra, Logic::QfBv, Logic::QfUf];
}

impl std::fmt::Display for Logic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name())
    }
}

const MAX_TERM_DEPTH: u32 = 2;
const MAX_FORMULA_DEPTH: u32 = 2;

/// Generate a single, fully deterministic SMT-LIB2 script for `logic` and
/// `seed`. Calling this twice with the same arguments always returns the
/// same string.
pub fn generate_script(logic: Logic, seed: u64) -> String {
    let mut rng = Rng::new(seed);
    match logic {
        Logic::QfLia => generate_linear_arith(&mut rng, false),
        Logic::QfLra => generate_linear_arith(&mut rng, true),
        Logic::QfBv => generate_bv(&mut rng),
        Logic::QfUf => generate_uf(&mut rng),
    }
}

// ========  ========
// QF_LIA / QF_LRA: shared linear-arithmetic generator
// ========  ========

fn fmt_arith_const(rng: &mut Rng, is_real: bool) -> String {
    let magnitude = rng.range_i64(0, 9);
    let negative = rng.chance(1, 3) && magnitude != 0;
    // SMT-LIB numerals/decimals are never written with a leading '-': a
    // negative literal must be spelled `(- 5)` / `(- 5.0)`.
    let literal = if is_real {
        let frac = rng.range_i64(0, 9);
        format!("{magnitude}.{frac}")
    } else {
        format!("{magnitude}")
    };
    if negative {
        format!("(- {literal})")
    } else {
        literal
    }
}

fn gen_linear_term(rng: &mut Rng, vars: &[String], is_real: bool, depth: u32) -> String {
    if depth == 0 || rng.chance(1, 3) {
        if !vars.is_empty() && rng.chance(1, 2) {
            vars[rng.index(vars.len())].clone()
        } else {
            fmt_arith_const(rng, is_real)
        }
    } else {
        match rng.index(4) {
            0 => {
                let n = rng.range_i64(2, 3) as usize;
                let parts: Vec<String> = (0..n)
                    .map(|_| gen_linear_term(rng, vars, is_real, depth - 1))
                    .collect();
                format!("(+ {})", parts.join(" "))
            }
            1 => {
                let a = gen_linear_term(rng, vars, is_real, depth - 1);
                let b = gen_linear_term(rng, vars, is_real, depth - 1);
                format!("(- {a} {b})")
            }
            2 => {
                // Scalar multiplication only: keeps the term linear so it
                // stays inside QF_LIA/QF_LRA rather than drifting into
                // QF_NIA/QF_NRA (variable*variable products).
                let c = fmt_arith_const(rng, is_real);
                let a = gen_linear_term(rng, vars, is_real, depth - 1);
                format!("(* {c} {a})")
            }
            _ => {
                let a = gen_linear_term(rng, vars, is_real, depth - 1);
                format!("(- {a})")
            }
        }
    }
}

const ARITH_REL_OPS: [&str; 6] = ["=", "<", "<=", ">", ">=", "distinct"];

fn gen_arith_atom(rng: &mut Rng, vars: &[String], is_real: bool) -> String {
    let op = ARITH_REL_OPS[rng.index(ARITH_REL_OPS.len())];
    let lhs = gen_linear_term(rng, vars, is_real, MAX_TERM_DEPTH);
    let rhs = gen_linear_term(rng, vars, is_real, MAX_TERM_DEPTH);
    format!("({op} {lhs} {rhs})")
}

/// Combine leaf atoms produced by `gen_atom` into a Boolean formula using
/// `and`/`or`/`not`, bottoming out at `depth == 0`.
fn gen_bool_formula(
    rng: &mut Rng,
    depth: u32,
    gen_atom: &mut dyn FnMut(&mut Rng) -> String,
) -> String {
    if depth == 0 || rng.chance(2, 5) {
        gen_atom(rng)
    } else {
        match rng.index(3) {
            0 => {
                let n = rng.range_i64(2, 3) as usize;
                let parts: Vec<String> = (0..n)
                    .map(|_| gen_bool_formula(rng, depth - 1, gen_atom))
                    .collect();
                format!("(and {})", parts.join(" "))
            }
            1 => {
                let n = rng.range_i64(2, 3) as usize;
                let parts: Vec<String> = (0..n)
                    .map(|_| gen_bool_formula(rng, depth - 1, gen_atom))
                    .collect();
                format!("(or {})", parts.join(" "))
            }
            _ => format!("(not {})", gen_bool_formula(rng, depth - 1, gen_atom)),
        }
    }
}

fn generate_linear_arith(rng: &mut Rng, is_real: bool) -> String {
    let sort_name = if is_real { "Real" } else { "Int" };
    let logic = if is_real { Logic::QfLra } else { Logic::QfLia };

    let num_vars = rng.range_i64(2, 4) as usize;
    let vars: Vec<String> = (0..num_vars).map(|i| format!("x{i}")).collect();
    let num_assertions = rng.range_i64(2, 5) as usize;

    let mut out = String::new();
    let _ = writeln!(out, "; Auto-generated differential-test case ({logic})");
    let _ = writeln!(out, "(set-logic {logic})");
    for v in &vars {
        let _ = writeln!(out, "(declare-const {v} {sort_name})");
    }
    for _ in 0..num_assertions {
        let formula = gen_bool_formula(rng, MAX_FORMULA_DEPTH, &mut |r| {
            gen_arith_atom(r, &vars, is_real)
        });
        let _ = writeln!(out, "(assert {formula})");
    }
    let _ = writeln!(out, "(check-sat)");
    out
}

// ========  ========
// QF_BV
// ========  ========

const BV_BINOPS: [&str; 6] = ["bvadd", "bvsub", "bvmul", "bvand", "bvor", "bvxor"];
const BV_REL_OPS: [&str; 6] = ["=", "bvult", "bvule", "bvugt", "bvuge", "distinct"];

fn fmt_bv_const(rng: &mut Rng, width: u32) -> String {
    let value = rng.next_below(1u64 << width);
    let width = width as usize;
    format!("#b{value:0width$b}")
}

fn gen_bv_term(rng: &mut Rng, vars: &[String], width: u32, depth: u32) -> String {
    if depth == 0 || rng.chance(1, 3) {
        if !vars.is_empty() && rng.chance(1, 2) {
            vars[rng.index(vars.len())].clone()
        } else {
            fmt_bv_const(rng, width)
        }
    } else if rng.chance(1, 7) {
        // Unary: bitwise negation or two's-complement negation.
        let a = gen_bv_term(rng, vars, width, depth - 1);
        if rng.chance(1, 2) {
            format!("(bvnot {a})")
        } else {
            format!("(bvneg {a})")
        }
    } else {
        let op = BV_BINOPS[rng.index(BV_BINOPS.len())];
        let a = gen_bv_term(rng, vars, width, depth - 1);
        let b = gen_bv_term(rng, vars, width, depth - 1);
        format!("({op} {a} {b})")
    }
}

fn gen_bv_atom(rng: &mut Rng, vars: &[String], width: u32) -> String {
    let op = BV_REL_OPS[rng.index(BV_REL_OPS.len())];
    let lhs = gen_bv_term(rng, vars, width, MAX_TERM_DEPTH);
    let rhs = gen_bv_term(rng, vars, width, MAX_TERM_DEPTH);
    format!("({op} {lhs} {rhs})")
}

fn generate_bv(rng: &mut Rng) -> String {
    let width: u32 = if rng.chance(1, 2) { 4 } else { 8 };
    let num_vars = rng.range_i64(2, 4) as usize;
    let vars: Vec<String> = (0..num_vars).map(|i| format!("x{i}")).collect();
    let num_assertions = rng.range_i64(2, 5) as usize;

    let mut out = String::new();
    let _ = writeln!(
        out,
        "; Auto-generated differential-test case (QF_BV, width={width})"
    );
    let _ = writeln!(out, "(set-logic QF_BV)");
    for v in &vars {
        let _ = writeln!(out, "(declare-const {v} (_ BitVec {width}))");
    }
    for _ in 0..num_assertions {
        let formula = gen_bool_formula(rng, MAX_FORMULA_DEPTH, &mut |r| {
            gen_bv_atom(r, &vars, width)
        });
        let _ = writeln!(out, "(assert {formula})");
    }
    let _ = writeln!(out, "(check-sat)");
    out
}

// ========  ========
// QF_UF
// ========  ========

fn gen_uf_term(rng: &mut Rng, consts: &[String], depth: u32) -> String {
    if depth == 0 || rng.chance(1, 3) {
        consts[rng.index(consts.len())].clone()
    } else if rng.chance(1, 2) {
        let a = gen_uf_term(rng, consts, depth - 1);
        format!("(f {a})")
    } else {
        let a = gen_uf_term(rng, consts, depth - 1);
        let b = gen_uf_term(rng, consts, depth - 1);
        format!("(g {a} {b})")
    }
}

fn gen_uf_atom(rng: &mut Rng, consts: &[String]) -> String {
    let op = if rng.chance(1, 2) { "=" } else { "distinct" };
    let lhs = gen_uf_term(rng, consts, MAX_TERM_DEPTH);
    let rhs = gen_uf_term(rng, consts, MAX_TERM_DEPTH);
    format!("({op} {lhs} {rhs})")
}

fn generate_uf(rng: &mut Rng) -> String {
    let num_consts = rng.range_i64(3, 5) as usize;
    let consts: Vec<String> = (0..num_consts).map(|i| format!("c{i}")).collect();
    let num_assertions = rng.range_i64(2, 5) as usize;

    let mut out = String::new();
    let _ = writeln!(out, "; Auto-generated differential-test case (QF_UF)");
    let _ = writeln!(out, "(set-logic QF_UF)");
    let _ = writeln!(out, "(declare-sort U 0)");
    for c in &consts {
        let _ = writeln!(out, "(declare-const {c} U)");
    }
    let _ = writeln!(out, "(declare-fun f (U) U)");
    let _ = writeln!(out, "(declare-fun g (U U) U)");
    for _ in 0..num_assertions {
        let formula = gen_bool_formula(rng, MAX_FORMULA_DEPTH, &mut |r| gen_uf_atom(r, &consts));
        let _ = writeln!(out, "(assert {formula})");
    }
    let _ = writeln!(out, "(check-sat)");
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic_for_fixed_seed() {
        for logic in Logic::ALL {
            let a = generate_script(logic, 12345);
            let b = generate_script(logic, 12345);
            assert_eq!(a, b, "generation for {logic} must be deterministic");
        }
    }

    #[test]
    fn different_seeds_usually_differ() {
        for logic in Logic::ALL {
            let a = generate_script(logic, 1);
            let b = generate_script(logic, 2);
            assert_ne!(a, b, "seeds 1 and 2 for {logic} produced identical scripts");
        }
    }

    #[test]
    fn scripts_are_well_formed_smtlib() {
        for logic in Logic::ALL {
            for seed in 0..25u64 {
                let script = generate_script(logic, seed);
                assert!(
                    script.contains(&format!("(set-logic {})", logic.name())),
                    "{logic} seed {seed} missing set-logic header:\n{script}"
                );
                assert!(
                    script.trim_end().ends_with("(check-sat)"),
                    "{logic} seed {seed} missing trailing check-sat:\n{script}"
                );
                // Every open paren must have a matching close paren (a cheap
                // syntactic sanity check that catches generator bugs before
                // they ever reach a solver).
                let opens = script.chars().filter(|&c| c == '(').count();
                let closes = script.chars().filter(|&c| c == ')').count();
                assert_eq!(
                    opens, closes,
                    "{logic} seed {seed} has unbalanced parens:\n{script}"
                );
            }
        }
    }

    #[test]
    fn qf_lia_terms_never_multiply_two_variables() {
        // A cheap textual regression guard: since `fmt_arith_const` never
        // emits a bare variable, any `(* ...)` node's first argument is
        // always a numeral/`(- numeral)`, never `x<N>`. This just spots the
        // obvious "generator regressed into nonlinear terms" mistake.
        for seed in 0..50u64 {
            let script = generate_script(Logic::QfLia, seed);
            for line in script.lines() {
                if let Some(pos) = line.find("(* x") {
                    panic!(
                        "seed {seed}: found variable-first multiplication at byte {pos}: {line}"
                    );
                }
            }
        }
    }

    #[test]
    fn rng_range_i64_stays_in_bounds() {
        let mut rng = Rng::new(7);
        for _ in 0..1000 {
            let v = rng.range_i64(-3, 6);
            assert!((-3..=6).contains(&v));
        }
    }

    #[test]
    fn rng_index_stays_in_bounds() {
        let mut rng = Rng::new(99);
        for _ in 0..1000 {
            let v = rng.index(5);
            assert!(v < 5);
        }
    }
}
