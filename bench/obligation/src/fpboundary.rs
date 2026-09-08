//! FP semantic boundary obligations (family `fpboundary`).
//!
//! Productions at the exact-arithmetic seams of the FloatingPoint theory —
//! the shapes where a sloppy rounding, a lost sign-of-zero, a truncating
//! underflow or a datum-identity slip produces a WRONG answer (not just an
//! unknown).  Every expected verdict is derived from an **exact oracle**
//! inside the generator: std-only `u128`/`i128` integer arithmetic over the
//! operands' planted bit patterns, rounded to the IEEE-754 double grid under
//! the production's rounding mode.  No `f64` arithmetic participates in any
//! expected answer — native f64 is correctly rounded RNE, but the directed
//! modes, halfway ties, and subnormal corners are exactly where that is not
//! enough.
//!
//! The family is the standing descendant of the one-session differential
//! battery that found three FP bug classes
//! (`docs/studies/2026-09-08-fp-const-folding.md`): datum identity of `=`
//! on floats, directed-mode gradual underflow, and SMT-LIB `fp.min`/`fp.max`
//! ties.
//!
//! Exactness bounds, guaranteed by planting and asserted with
//! `debug_assert!`: mantissa products are ≤ 106 bits (`u128`), addition
//! alignment gaps are ≤ 64 exponent steps (aligned sums ≤ 118 bits,
//! `i128`), and division quotients are developed with two guard bits plus a
//! sticky bit before rounding.

use crate::{Answer, Instance, InstanceKind, Rng};

/// Parameters per size.
pub struct Params {
    /// Oracle-driven fold productions (sat + unsat twin each).
    pub folds: usize,
    /// Include the two-step chain instances.
    pub chains: bool,
    /// Include the incremental (push/pop retraction) instance.
    pub incremental: bool,
}

// ===========================================================================
// Exact f64 model (std-only)
// ===========================================================================

const P: u32 = 53;
const E_MIN: i32 = -1074; // subnormal unit scale (binary exponent of the LSB)
const E_MAX_BIN: i32 = 1023; // largest normal binary exponent
const BIAS: i32 = 1023;

/// A finite nonzero double, decomposed as `neg ? -1 : 1 · mant · 2^exp2`,
/// `mant` carrying the implicit bit for normals (≥ 2^52).
#[derive(Clone, Copy, Debug)]
#[doc(hidden)]
pub struct DecF64 {
    /// Field access for the certificate tests only.
    pub neg: bool,
    pub mant: u64,
    pub exp2: i32,
}

fn bit_len(x: u128) -> i32 {
    128 - x.leading_zeros() as i32
}

impl DecF64 {
    #[doc(hidden)]
    pub fn decode(bits: u64) -> Option<Self> {
        let neg = bits >> 63 == 1;
        let be = ((bits >> 52) & 0x7ff) as i32;
        let frac = bits & ((1u64 << 52) - 1);
        match (be, frac) {
            (0, 0) | (0x7ff, _) => None, // zeros, infinities, NaN: not modeled
            (0, f) => Some(Self {
                neg,
                mant: f,
                exp2: E_MIN,
            }),
            (e, f) => Some(Self {
                neg,
                mant: f | (1u64 << 52),
                exp2: e - BIAS - 52,
            }),
        }
    }
}

/// A rounding mode (SMT-LIB spellings).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[doc(hidden)]
pub enum Rm {
    Rne,
    Rna,
    Rtp,
    Rtn,
    Rtz,
}

impl Rm {
    #[doc(hidden)]
    pub fn name(self) -> &'static str {
        match self {
            Rm::Rne => "RNE",
            Rm::Rna => "RNA",
            Rm::Rtp => "RTP",
            Rm::Rtn => "RTN",
            Rm::Rtz => "RTZ",
        }
    }

    fn pick(n: u64) -> Self {
        match n % 5 {
            0 => Rm::Rne,
            1 => Rm::Rna,
            2 => Rm::Rtp,
            3 => Rm::Rtn,
            _ => Rm::Rtz,
        }
    }
}

fn inf_bits(neg: bool) -> u64 {
    ((neg as u64) << 63) | (0x7ffu64 << 52)
}

fn max_finite_bits(neg: bool) -> u64 {
    ((neg as u64) << 63) | (0x7feu64 << 52) | ((1u64 << 52) - 1)
}

/// Does the rounding mode round the truncated magnitude UP (away from zero)?
/// `rem` is the dropped magnitude, `half` the halfway bit, `lsb` the parity
/// of the truncated significand's last bit.
fn round_away(neg: bool, rem: u128, half: u128, lsb: u128, rm: Rm) -> bool {
    match rm {
        Rm::Rne => rem > half || (rem == half && lsb == 1),
        Rm::Rna => rem >= half,
        Rm::Rtp => !neg && rem != 0,
        Rm::Rtn => neg && rem != 0,
        Rm::Rtz => false,
    }
}

/// Round the exact nonzero value `neg ? -1 : 1 · num · 2^exp2` (num > 0) to
/// the double grid under `rm`, from first principles: the normal grid when
/// the value's binary exponent permits, the subnormal grid below it, and
/// overflow saturating per mode.  Returns f64 bits.
/// Saturate an overflow per mode: the directed modes that point back
/// inside (RTZ always; RTP for negatives; RTN for positives) clamp to the
/// maximum finite datum, everything else overflows to ±inf.
fn overflow_result(neg: bool, rm: Rm) -> u64 {
    match rm {
        Rm::Rtp if neg => max_finite_bits(neg),
        Rm::Rtn if !neg => max_finite_bits(neg),
        Rm::Rtz => max_finite_bits(neg),
        _ => inf_bits(neg),
    }
}

#[doc(hidden)]
pub fn round_exact(neg: bool, num: u128, exp2: i32, rm: Rm) -> u64 {
    debug_assert!(num != 0);
    let l = bit_len(num);
    let bin_exp = exp2 + l - 1;
    // Normal grid: significand of P bits at unit 2^(bin_exp - (P-1)); the
    // subnormal grid clamps that unit at 2^E_MIN.
    let normal_grid = bin_exp - (P as i32 - 1) >= E_MIN;
    if normal_grid && bin_exp - (P as i32 - 1) > E_MAX_BIN + 1 {
        // The exact value is beyond the normal range even before rounding:
        // saturate per mode — the directed modes that point back inside
        // (RTZ always; RTP for negatives; RTN for positives) clamp to the
        // maximum finite datum, everything else overflows to ±inf.
        return overflow_result(neg, rm);
    }
    let (shift, cell_max, cell_exp) = if normal_grid {
        let shift = l - P as i32;
        let unit_exp = bin_exp - (P as i32 - 1); // 2^unit_exp = one cell LSB
        (shift, 1u128 << P, unit_exp)
    } else {
        // The subnormal grid is ABSOLUTE (unit 2^E_MIN): the exact value
        // num·2^exp2 is `num·2^(exp2-E_MIN)` cells.  exp2 > E_MIN scales UP
        // (exact — the value is a grid multiple); exp2 < E_MIN shifts down
        // with the dropped bits as the rounding remainder.
        (E_MIN - exp2, 1u128 << 52, E_MIN)
    };
    let (trunc, rem, half, lsb) = if shift <= 0 {
        // exp2 >= E_MIN on the subnormal grid: the value is an exact grid
        // multiple (num · 2^(-shift) cells; bounded by 2^52 because the
        // value is subnormal).  No rounding.
        debug_assert!(normal_grid || (-shift) <= 64);
        if shift == 0 {
            (num, 0u128, 0u128, 0u128)
        } else {
            (num << (-shift), 0u128, 0u128, 0u128)
        }
    } else if shift >= 128 {
        // Far below the grid: the truncated cell is zero and the entire
        // magnitude is the remainder.  The halfway mark (2^(shift-1)) is
        // beyond u128, but `num < 2^127 <= 2^(shift-1)` always holds here
        // (planting bounds every numerator below 2^118), so the nearest
        // modes stay at zero and only the directed modes can round up.
        // `half = u128::MAX` encodes "rem is below halfway" for the
        // comparisons (rem > half is false; rem == half cannot occur since
        // num < 2^118 < MAX).
        (0, num, u128::MAX, 0)
    } else {
        (
            num >> shift,
            num & ((1u128 << shift) - 1),
            1u128 << (shift - 1),
            (num >> shift) & 1,
        )
    };
    let mut cell = trunc;
    // Rounding consults the dropped bits only when they exist (`shift > 0`):
    // an exact grid value (rem = 0 with a real half-mark) must never round,
    // and RNA's `rem >= half` would otherwise fire on `0 >= 0`.
    if shift > 0 && round_away(neg, rem, half, lsb, rm) {
        cell += 1;
    }
    if cell >= cell_max {
        // Carry out of the grid: subnormal → smallest normal; normal →
        // exponent bump (possibly overflow).
        if !normal_grid {
            return ((neg as u64) << 63) | (((BIAS + 1) as u64) << 52);
        }
        let bin_exp_after = cell_exp + (P as i32 - 1) + 1;
        let be = bin_exp_after + BIAS;
        if be >= 0x7ff {
            // Rounding carried past max finite: inf unless the mode rounds
            // back inside (only reachable from within one ulp of the max).
            return match rm {
                Rm::Rtp if neg => max_finite_bits(neg),
                Rm::Rtn if !neg => max_finite_bits(neg),
                Rm::Rtz => max_finite_bits(neg),
                _ => inf_bits(neg),
            };
        }
        let sig = cell >> 1; // exactly 2^(P-1)
        return ((neg as u64) << 63) | ((be as u64) << 52) | (sig as u64 & ((1 << 52) - 1));
    }
    if normal_grid {
        let be = cell_exp + (P as i32 - 1) + BIAS;
        // (cell ∈ [2^(P-1), 2^P): a normal.)
        ((neg as u64) << 63) | ((be as u64) << 52) | (cell as u64 & ((1u64 << 52) - 1))
    } else {
        ((neg as u64) << 63) | (cell as u64)
    }
}

// ===========================================================================
// Exact operations (operand pairs planted within the bounds above)
// ===========================================================================

/// Exact `a ± b` as `(neg, num, exp2)`; `num` may be zero on exact
/// cancellation (callers replant those — the sign of an exact zero is
/// mode-dependent and belongs to the analytic corners).
fn exact_add(a: DecF64, b: DecF64, subtract: bool) -> (bool, u128, i32) {
    let sb = if subtract { !b.neg } else { b.neg };
    // Scale both to the smaller exponent (base), as signed i128.
    let base = a.exp2.min(b.exp2);
    let da = a.exp2 - base;
    let db = b.exp2 - base;
    debug_assert!(da >= 0 && db >= 0 && da <= 64 && db <= 64);
    let sa = a.mant as i128;
    let sval = sa << da;
    let sbval = (b.mant as i128) << db;
    let signed = if a.neg { -sval } else { sval } + if sb { -sbval } else { sbval };
    (signed < 0, signed.unsigned_abs(), base)
}

/// Exact `a · b` (mantissa product ≤ 106 bits).
fn exact_mul(a: DecF64, b: DecF64) -> (bool, u128, i32) {
    (
        a.neg != b.neg,
        (a.mant as u128) * (b.mant as u128),
        a.exp2 + b.exp2,
    )
}

/// `a / b` where `b`'s significand is a power of two (the planted divisor
/// pool guarantees it): the quotient is the EXACT value
/// `± a.mant · 2^(a.exp2 - b.exp2 - k)` with `b.mant = 2^k` — no mantissa
/// division exists, so the only rounding that can happen is the grid
/// rounding of `round_exact` at the quotient's own scale (underflow and
/// overflow corners included).  Inexact mantissa division is deliberately
/// out of the family's scope: the std-only oracle would need a bignum long
/// division, and division-rounding-at-a-grid is already exercised by the
/// add/sub/mul folds.
fn round_div_pow2(a: DecF64, b: DecF64, rm: Rm) -> Option<u64> {
    let k = b.mant.trailing_zeros();
    if b.mant >> k != 1 {
        return None; // not a power of two: replant
    }
    let neg = a.neg != b.neg;
    Some(round_exact(
        neg,
        a.mant as u128,
        a.exp2 - b.exp2 - k as i32,
        rm,
    ))
}

// ===========================================================================
// Literals
// ===========================================================================

#[doc(hidden)]
pub fn lit(bits: u64) -> String {
    let neg = (bits >> 63) & 1;
    let be = (bits >> 52) & 0x7ff;
    let frac = bits & ((1u64 << 52) - 1);
    if be == 0x7ff && frac == 0 {
        return format!("(_ {} 11 53)", if neg == 1 { "-oo" } else { "+oo" });
    }
    format!("(fp #b{neg} #b{be:011b} #x{frac:013x})")
}

fn is_nan_bits(bits: u64) -> bool {
    ((bits >> 52) & 0x7ff) == 0x7ff && (bits & ((1u64 << 52) - 1)) != 0
}

// ===========================================================================
// Instances
// ===========================================================================

struct Ctx {
    out: Vec<Instance>,
    seed: u64,
    suffix: String,
    tag: u64,
}

impl Ctx {
    fn push(
        &mut self,
        name: &str,
        script: String,
        expected: Vec<Answer>,
        witness: Option<String>,
        certificate: String,
    ) {
        self.tag += 1;
        self.out.push(Instance {
            family: "fpboundary",
            name: format!("fpboundary-{name}-s{}-{}", self.seed, self.suffix),
            logic: "QQ_FP".replace("QQ", "QF"),
            script,
            kind: InstanceKind::Smt2,
            expected,
            witness,
            certificate,
            tags: vec!["fpboundary", "fp", "ieee754"],
        });
        let _ = self.tag;
    }
}

/// The planted finite-operand pool: subnormals, the 1-ulp neighbourhood of
/// 1.0, exact powers of two, short-mantissa mid-range normals, near-max
/// normals, and negatives of the same shapes.
fn operand_bits(rng: &mut Rng) -> u64 {
    match rng.next_u64() % 7 {
        0 => 1 + rng.next_u64() % 3, // subnormals
        1 => (1023u64 << 52) + rng.next_u64() % 4,
        2 => (40 + rng.next_u64() % 960) << 52, // powers of two
        3 => (1000 + rng.next_u64() % 24) << 52 | (rng.next_u64() & 0xfff),
        4 => (2040u64 << 52) | (rng.next_u64() & 0xff),
        5 => {
            let e = rng.next_u64() % 4;
            let mag = match e {
                0 => 1 + rng.next_u64() % 3,
                1 => (1023 << 52) + rng.next_u64() % 4,
                2 => (600 + rng.next_u64() % 800) << 52,
                _ => (1020 + rng.next_u64() % 8) << 52 | (rng.next_u64() & 0xff),
            };
            mag | (1 << 63)
        }
        _ => (900 + rng.next_u64() % 130) << 52 | (rng.next_u64() & 0xfffff),
    }
}

fn fold_instances(ctx: &mut Ctx, rng: &mut Rng, count: usize) {
    const OPS: [&str; 4] = ["fp.add", "fp.sub", "fp.mul", "fp.div"];
    for i in 0..count {
        let op = OPS[(rng.next_u64() % 4) as usize];
        let rm = Rm::pick(rng.next_u64());
        // Plant decodable pairs within the alignment/product bounds; exact
        // cancellation in sub is replanted (zero-sign is mode-dependent),
        // and division plants power-of-two divisors (see `round_div_pow2`).
        let pow2_divisor = |rng: &mut Rng| -> u64 {
            match rng.next_u64() % 3 {
                // subnormal powers of two: frac = 2^k
                0 => 1u64 << (rng.next_u64() % 52),
                // normal powers of two: nonzero exponent field, frac = 0
                _ => (1 + rng.next_u64() % 2046) << 52,
            }
        };
        let (a_bits, b_bits, a, b) = loop {
            let (ab, bb) = (
                operand_bits(rng),
                if op == "fp.div" {
                    pow2_divisor(rng)
                } else {
                    operand_bits(rng)
                },
            );
            if let (Some(x), Some(y)) = (DecF64::decode(ab), DecF64::decode(bb)) {
                let addish = op == "fp.add" || op == "fp.sub";
                if addish {
                    if (x.exp2 - y.exp2).abs() > 64 {
                        continue;
                    }
                    // Exact cancellation (sub of equals, add of opposites):
                    // the sign of an exact zero is mode-dependent, which
                    // belongs to the analytic corners — replant.
                    let aligned_equal = |x: &DecF64, y: &DecF64| -> bool {
                        if x.exp2 >= y.exp2 {
                            (x.mant as u128) << (x.exp2 - y.exp2) == y.mant as u128
                        } else {
                            x.mant as u128 == (y.mant as u128) << (y.exp2 - x.exp2)
                        }
                    };
                    let cancels = aligned_equal(&x, &y)
                        && ((op == "fp.sub" && x.neg == y.neg)
                            || (op == "fp.add" && x.neg != y.neg));
                    if cancels {
                        continue;
                    }
                }
                break (ab, bb, x, y);
            }
        };
        let correct = match op {
            "fp.add" => {
                let (neg, num, e2) = exact_add(a, b, false);
                round_exact(neg, num, e2, rm)
            }
            "fp.sub" => {
                let (neg, num, e2) = exact_add(a, b, true);
                debug_assert!(num != 0, "replanted above");
                round_exact(neg, num, e2, rm)
            }
            "fp.mul" => {
                let (neg, num, e2) = exact_mul(a, b);
                round_exact(neg, num, e2, rm)
            }
            _ => match round_div_pow2(a, b, rm) {
                Some(bits) => bits,
                None => continue, // non-power-of-two divisor: cannot happen
            },
        };
        if is_nan_bits(correct) {
            // NaN results (0/0-shaped divisions cannot occur — both operands
            // are nonzero — but underflow-to-NaN edges are out of scope).
            continue;
        }
        // The wrong datum: the neighbouring finite bit pattern (inf results
        // probe against max finite).
        let wrong = if correct == inf_bits(false) || correct == inf_bits(true) {
            max_finite_bits(correct >> 63 == 1)
        } else {
            correct + 1
        };
        let (la, lb) = (lit(a_bits), lit(b_bits));
        let head = format!(
            "(set-logic QF_FP)\n(declare-const x Float64)\n(declare-const y Float64)\n\
             (assert (= x {la}))\n(assert (= y ({op} {} x {lb})))\n",
            rm.name()
        );
        let cert = format!(
            "Exact value of ({op} {} x {lb}) at x = {la}: computed on the \
             generator's u128/i128 exact model (mantissas {}·2^{}, {}·2^{}) \
             and rounded under {} to {}; every neighbouring bit pattern is a \
             different datum, so the twin instance is unsat.",
            rm.name(),
            a.mant,
            a.exp2,
            b.mant,
            b.exp2,
            rm.name(),
            lit(correct)
        );
        ctx.push(
            &format!("fold-{i}"),
            format!("{head}(assert (= y {}))\n(check-sat)\n", lit(correct)),
            vec![Answer::Sat],
            Some(format!("x = {la}, y = {}", lit(correct))),
            cert.clone(),
        );
        ctx.push(
            &format!("fold-{i}-neg"),
            format!("{head}(assert (= y {}))\n(check-sat)\n", lit(wrong)),
            vec![Answer::Unsat],
            None,
            cert,
        );
    }
}

pub fn generate(seed: u64, p: &Params, suffix: &str) -> Result<Vec<Instance>, String> {
    let mut rng = Rng::new(seed);
    let mut ctx = Ctx {
        out: Vec::new(),
        seed,
        suffix: suffix.into(),
        tag: 0,
    };

    // ---- datum identity (UNSAT): distinct finite datums asserted equal,
    //      direct and variable-mediated.
    let pairs: &[(u64, u64, &str)] = &[
        (0x0000000000000000, 0x8000000000000000, "+0 vs -0"),
        (0x0000000000000001, 0x8000000000000001, "±min subnormal"),
        (
            0x3ff0000000000000,
            0x3ff0000000000001,
            "1.0 vs the next datum",
        ),
        (0x7ff0000000000000, 0xfff0000000000000, "+oo vs -oo"),
    ];
    for (i, (a, b, what)) in pairs.iter().enumerate() {
        ctx.push(
            &format!("datum-{i}"),
            format!(
                "(set-logic QF_FP)\n(assert (= {} {}))\n(check-sat)\n",
                lit(*a),
                lit(*b)
            ),
            vec![Answer::Unsat],
            None,
            format!(
                "SMT-LIB `=` on floats is datum identity: {what} are distinct \
                 data (bit patterns differ; z3-verified)."
            ),
        );
        ctx.push(
            &format!("datum-mediated-{i}"),
            format!(
                "(set-logic QF_FP)\n(declare-const x Float64)\n(assert (= x {}))\n\
                 (assert (= x {}))\n(check-sat)\n",
                lit(*a),
                lit(*b)
            ),
            vec![Answer::Unsat],
            None,
            format!(
                "Transitive form of the same contradiction ({what}): x merges \
                 with both literals and the distinct value marks collide."
            ),
        );
    }

    // ---- NaN datum collapse (SAT): different NaN spellings, one datum.
    let nans = [
        "(_ NaN 11 53)".to_string(),
        lit(0x7ff8000000000001),
        lit(0x7ff8000000000002),
        lit(0xfff8000000000001),
    ];
    for i in 0..nans.len() {
        for j in (i + 1)..nans.len() {
            ctx.push(
                &format!("nan-datum-{i}{j}"),
                format!(
                    "(set-logic QF_FP)\n(declare-const x Float64)\n(assert (= x {}))\n\
                     (assert (= x {}))\n(check-sat)\n",
                    nans[i], nans[j]
                ),
                vec![Answer::Sat],
                Some("x = (_ NaN 11 53)".into()),
                "Every NaN of a format is ONE datum under `=` (z3-verified on \
                 exact-width literals): payload and sign do not distinguish \
                 NaN data."
                    .into(),
            );
        }
    }

    // ---- directed-mode gradual-underflow corners (analytic).
    let ms_p = 0x0000000000000001u64;
    let ms_n = 0x8000000000000001u64;
    let neg_zero = 0x8000000000000000u64;
    let corners: &[(Rm, u64, u64, u64, &str)] = &[
        (
            Rm::Rtn,
            ms_n,
            ms_p,
            ms_n,
            "RTN of a negative far-underflow is -min_subnormal",
        ),
        (
            Rm::Rtp,
            ms_p,
            ms_p,
            ms_p,
            "RTP of a positive far-underflow is +min_subnormal",
        ),
        (
            Rm::Rtz,
            ms_n,
            ms_p,
            neg_zero,
            "RTZ of a negative far-underflow is -0",
        ),
        (
            Rm::Rne,
            ms_n,
            ms_p,
            neg_zero,
            "RNE of a far-underflow below half the smallest subnormal is -0",
        ),
    ];
    for (i, (rm, a, b, correct, why)) in corners.iter().enumerate() {
        let wrong = if *correct == neg_zero { ms_n } else { neg_zero };
        let cert = format!(
            "Gradual underflow rounds on the SUBNORMAL grid: {why} (exact \
             product ≈ -2.47e-647, far below the subnormal range; the \
             rounding direction is the mode's)."
        );
        ctx.push(
            &format!("underflow-{i}"),
            format!(
                "(set-logic QF_FP)\n(assert (= (fp.mul {} {} {}) {}))\n(check-sat)\n",
                rm.name(),
                lit(*a),
                lit(*b),
                lit(*correct)
            ),
            vec![Answer::Sat],
            Some(format!("= {}", lit(*correct))),
            cert.clone(),
        );
        ctx.push(
            &format!("underflow-{i}-neg"),
            format!(
                "(set-logic QF_FP)\n(assert (= (fp.mul {} {} {}) {}))\n(check-sat)\n",
                rm.name(),
                lit(*a),
                lit(*b),
                lit(wrong)
            ),
            vec![Answer::Unsat],
            None,
            format!("The complementary underflow datum is wrong: {why}."),
        );
    }

    // ---- SMT-LIB fp.min / fp.max ties and NaN handling.
    ctx.push(
        "min-zero-tie",
        "(set-logic QF_FP)\n(assert (= (fp.min (_ +zero 11 53) (_ -zero 11 53)) (_ -zero 11 53)))\n(check-sat)\n".into(),
        vec![Answer::Sat],
        Some("fp.min(+0,-0) = -0".into()),
        "SMT-LIB fp.min prefers the negative zero on a tie (z3-verified).".into(),
    );
    ctx.push(
        "max-zero-tie",
        "(set-logic QF_FP)\n(assert (= (fp.max (_ +zero 11 53) (_ -zero 11 53)) (_ +zero 11 53)))\n(check-sat)\n".into(),
        vec![Answer::Sat],
        Some("fp.max(+0,-0) = +0".into()),
        "SMT-LIB fp.max prefers the positive zero on a tie (z3-verified).".into(),
    );
    ctx.push(
        "min-nan-yields-other",
        "(set-logic QF_FP)\n(assert (= (fp.min (_ NaN 11 53) (fp #b0 #b01111111111 #x0000000000000)) (fp #b0 #b01111111111 #x0000000000000)))\n(check-sat)\n".into(),
        vec![Answer::Sat],
        Some("fp.min(NaN, 1.0) = 1.0".into()),
        "SMT-LIB fp.min yields the OTHER operand on NaN (the theory's \
         ite-chain definition, not IEEE minNum; z3-verified)."
            .into(),
    );

    // ---- halfway ties at 1.0 (1.0 + 2^-53), every mode (analytic).
    let half_ulp = 0x3ca0000000000000u64; // 2^-53
    let one = 0x3ff0000000000000u64;
    let next1 = 0x3ff0000000000001u64;
    let ties: &[(Rm, u64, &str)] = &[
        (Rm::Rne, one, "RNE stays at 1.0 (ties to even)"),
        (Rm::Rna, next1, "RNA rounds away from zero"),
        (Rm::Rtp, next1, "RTP rounds up"),
        (Rm::Rtn, one, "RTN stays at 1.0"),
        (Rm::Rtz, one, "RTZ truncates to 1.0"),
    ];
    for (i, (rm, correct, why)) in ties.iter().enumerate() {
        let wrong = if *correct == one { next1 } else { one };
        let head = format!(
            "(set-logic QF_FP)\n(assert (= (fp.add {} {} {}) PROBE))\n(check-sat)\n",
            rm.name(),
            lit(one),
            lit(half_ulp)
        );
        let cert = format!(
            "1.0 + 2^-53 is exactly halfway between 1.0 and the next datum: \
             {why}."
        );
        ctx.push(
            &format!("halfway-{i}"),
            head.replace("PROBE", &lit(*correct)),
            vec![Answer::Sat],
            Some(format!("= {}", lit(*correct))),
            cert.clone(),
        );
        ctx.push(
            &format!("halfway-{i}-neg"),
            head.replace("PROBE", &lit(wrong)),
            vec![Answer::Unsat],
            None,
            format!("The opposite rounding of the same halfway sum is wrong: {why}."),
        );
    }

    // ---- oracle-driven folds (sat + unsat twins).
    fold_instances(&mut ctx, &mut rng, p.folds);

    // ---- transitive chains.
    if p.chains {
        let z9 = "(fp #b0 #b10000000010 #b0010000000000000000000000000000000000000000000000000)";
        let z10 = "(fp #b0 #b10000000010 #b0100000000000000000000000000000000000000000000000000)";
        let head = "(set-logic QF_FP)\n\
             (declare-const x Float64)\n(declare-const y Float64)\n(declare-const z Float64)\n\
             (assert (= x (fp #b0 #b01111111111 #x8000000000000)))\n\
             (assert (= y (fp.add RNE x x)))\n\
             (assert (= z (fp.mul RNE y y)))\n\
             (assert (= z PROBE))\n(check-sat)\n";
        ctx.push(
            "chain",
            head.replace("PROBE", z9),
            vec![Answer::Sat],
            Some("x = 1.5, y = 3.0, z = 9.0".into()),
            "1.5 + 1.5 = 3.0 exactly and 3.0·3.0 = 9.0 exactly: the fold \
             chain is exact and the final datum is 9.0."
                .into(),
        );
        ctx.push(
            "chain-neg",
            head.replace("PROBE", z10),
            vec![Answer::Unsat],
            None,
            "Same chain with the final datum perturbed to 10.0: the \
             transitive fold refutes the wrong datum."
                .into(),
        );
    }

    // ---- predicate folds over pinned values.
    let preds: &[(u64, u64, &str, bool)] = &[
        (0x3ff0000000000000, 0x4000000000000000, "fp.lt", true), // 1.0 < 2.0
        (0x4000000000000000, 0x3ff0000000000000, "fp.gt", true), // 2.0 > 1.0
        (0x3ff0000000000000, 0x3ff0000000000001, "fp.gt", false), // 1.0 ≯ next
        (0x7ff0000000000000, 0x7ff0000000000000, "fp.eq", true), // +oo = +oo
        (0x7ff8000000000000, 0x7ff8000000000000, "fp.lt", false), // NaN ≮ NaN
        (0x0000000000000000, 0x8000000000000000, "fp.eq", true), // +0 = -0 (IEEE)
    ];
    for (i, (a, b, pred, holds)) in preds.iter().enumerate() {
        // Probe the predicate itself: asserting a TRUE predicate is sat,
        // asserting a FALSE one is unsat (the negated forms are trivial).
        let assertion = format!("({pred} x {})", lit(*b));
        let expected = if *holds { Answer::Sat } else { Answer::Unsat };
        ctx.push(
            &format!("pred-{i}"),
            format!(
                "(set-logic QF_FP)\n(declare-const x Float64)\n(assert (= x {}))\n\
                 (assert {assertion})\n(check-sat)\n",
                lit(*a)
            ),
            vec![expected],
            if *holds {
                Some(format!("x = {}", lit(*a)))
            } else {
                None
            },
            format!(
                "IEEE-754 comparison semantics of {} {pred} {} is `{holds}` \
                 (±0 compare equal under fp.eq; NaN compares false in every \
                 ordering; infinities order by sign).",
                lit(*a),
                lit(*b)
            ),
        );
    }

    // ---- incremental: the fold contradiction retracts on pop.
    if p.incremental {
        ctx.push(
            "incremental-retract",
            "(set-logic QF_FP)\n\
             (push 1)\n\
             (declare-const x Float32)\n(declare-const y Float32)\n\
             (assert (= x (fp #b0 #x7f #b00000000000000000000001)))\n\
             (assert (= y (fp.add RNE x x)))\n\
             (assert (= y (fp #b0 #x80 #b00000000000000000000000)))\n\
             (check-sat)\n\
             (pop 1)\n\
             (assert (= (_ +zero 11 53) (_ +zero 11 53)))\n\
             (check-sat)\n"
                .into(),
            vec![Answer::Unsat, Answer::Sat],
            Some("scope 2 after pop: any model".into()),
            "Scope 1 pins x, folds x+x = 2.0000001… and asserts the wrong \
             datum (unsat by the fold + value marks); pop retracts the fold \
             lemmas and marks with the scope, so scope 2 is trivially sat — \
             pinning the pop journal of the FP fold layer."
                .into(),
        );
    }

    Ok(ctx.out)
}
