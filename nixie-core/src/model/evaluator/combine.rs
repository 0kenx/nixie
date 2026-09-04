//! Pure operand combiners for the model evaluator.
//!
//! Everything here is a *function of already-evaluated operand values*: no
//! access to the model, the cache, or the term manager, and no recursion into
//! sub-terms. That separation is what lets [`super::ModelEvaluator::eval`] be a
//! flat loop over an explicit frame stack – the driver decides *when* an
//! operator's operands are available, this module decides *what* the operator
//! computes from them.
//!
//! Reference: Z3's `model_evaluator.cpp` splits the same way, with the
//! `model_evaluator_cfg` reduction hooks holding the per-operator semantics.

use super::EvalResult;
use crate::ast::{TermId, str_fold};
use crate::model::Value;
#[allow(unused_imports)]
use crate::prelude::*;
use num_bigint::BigInt;
use num_rational::Rational64;
use num_traits::{CheckedDiv, CheckedSub, ToPrimitive};

// ======== Bitvector arithmetic helpers ========
//
// `Value::BitVec` stores a bitvector as `(declared_width: u32, magnitude:
// u64)` – the magnitude is capped at 64 bits regardless of the declared
// width (see the `BitVecConst` arm of `ModelEvaluator::eval_leaf` for why: a
// magnitude that does not fit `u64` is surfaced as an explicit error rather
// than fabricated). The helpers below encode that representation's
// consequences once, instead of re-deriving them at every BV eval site:
//
// - For `width <= 64` the magnitude is an exact `width`-bit two's
//   complement value, so sign/shift/div-by-zero handling follows the
//   SMT-LIB `FixedSizeBitVectors` theory directly.
// - For `width > 64`, only magnitudes `< 2^64 <= 2^(width-1)` are ever
//   representable, so such values are *always* non-negative in their true
//   `width`-bit interpretation – the "effective width" for sign/shift
//   purposes is therefore capped at 64.

/// Effective width used for masking/sign checks: `Value::BitVec`'s
/// magnitude cannot exceed 64 bits no matter what `width` is declared as.
fn bv_eff_width(width: u32) -> u32 {
    width.min(64)
}

/// The SMT-LIB bitvector modulus mask for `width` bits, capped at the
/// 64-bit magnitude `Value::BitVec` can represent.
pub(super) fn bv_mask(width: u32) -> u64 {
    let w = bv_eff_width(width);
    if w >= 64 { u64::MAX } else { (1u64 << w) - 1 }
}

/// Whether the `width`-bit magnitude `v` (already masked to its low bits)
/// is negative under two's complement. Always `false` for `width > 64`
/// (see module-level doc above): such values can never have a set sign
/// bit within the representable magnitude range.
fn bv_is_negative(width: u32, v: u64) -> bool {
    let w = bv_eff_width(width);
    if w == 0 || width > 64 {
        return false;
    }
    let sign_bit = if w == 64 { 1u64 << 63 } else { 1u64 << (w - 1) };
    v & sign_bit != 0
}

/// Two's complement negation of a `width`-bit magnitude.
fn bv_negate(width: u32, v: u64) -> u64 {
    v.wrapping_neg() & bv_mask(width)
}

/// Compare two `width`-bit magnitudes as signed two's-complement
/// integers. Within a sign-agreeing pair, unsigned (bit-pattern) order
/// already matches signed order in two's complement, so only
/// negative-vs-non-negative needs special-casing.
fn bv_signed_cmp(width: u32, a: u64, b: u64) -> core::cmp::Ordering {
    match (bv_is_negative(width, a), bv_is_negative(width, b)) {
        (false, false) | (true, true) => a.cmp(&b),
        (true, false) => core::cmp::Ordering::Less,
        (false, true) => core::cmp::Ordering::Greater,
    }
}

/// The common width and the two magnitudes of a binary bit-vector operator,
/// or the error the operator reports for operands it cannot use.
///
/// Every width-checking BV operator reported exactly these two messages, so
/// they are produced in one place rather than repeated per operator.
fn bv_operands(a: &Value, b: &Value, op: &str) -> Result<(u32, u64, u64), EvalResult> {
    match (a, b) {
        (Value::BitVec(w1, v1), Value::BitVec(w2, v2)) => {
            if w1 == w2 {
                Ok((*w1, *v1, *v2))
            } else {
                Err(EvalResult::Error(format!("{op}: width mismatch")))
            }
        }
        _ => Err(EvalResult::Error(format!("{op}: expected bitvectors"))),
    }
}

/// Normalize a rational result: an integral rational is reported as
/// `Value::Int`, matching the arithmetic arms of the recursive evaluator.
fn from_rational(r: Rational64) -> EvalResult {
    if *r.denom() == 1 {
        EvalResult::Ok(Value::Int(*r.numer()))
    } else {
        EvalResult::Ok(Value::Rational(r))
    }
}

/// The error an arithmetic operator reports when its exact result is not
/// representable.
///
/// `Value` arithmetic is fixed width – `i64` integers and `Rational64` reals –
/// so an overflowing result has no faithful `Value`. Every arithmetic arm is
/// written with `checked_*` so that this is what the caller gets, in *both*
/// build profiles: an unchecked `+`/`-`/`*` aborts a debug build with `attempt
/// to … with overflow` and, in release, silently wraps to a wrong model value,
/// which is worse. Same contract as the `IntConst` / `BitVecConst` arms of
/// [`super::ModelEvaluator::open`].
pub(super) fn arith_overflow(op: &str) -> EvalResult {
    EvalResult::Error(format!(
        "{op}: result is not representable in the fixed-width arithmetic \
         ModelEvaluator uses (i64 integers, Rational64 reals)"
    ))
}

/// A fixed-arity operator: everything whose operands the driver evaluates
/// eagerly, left to right, before combining them.
///
/// The n-ary and short-circuiting operators (`and`, `or`, `distinct`, `+`,
/// `*`, `ite`) are *not* here – their evaluation order depends on the operand
/// values, so they live in the driver's [`super::Op`] instead.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum EagerKind {
    /// `not`
    Not,
    /// `xor`
    Xor,
    /// `=>`
    Implies,
    /// `=`
    Eq,
    /// `-` (binary)
    Sub,
    /// `div` (`int_sorted`) or `/`
    Div {
        /// Whether the numerator's *sort* is Int, which selects Euclidean
        /// integer division over exact rational division.
        int_sorted: bool,
    },
    /// `mod`
    Mod,
    /// unary `-`
    Neg,
    /// `<` – also used for `>` with the operands swapped.
    Lt,
    /// `<=` – also used for `>=` with the operands swapped.
    Le,
    /// `bvnot`
    BvNot,
    /// One of the binary bit-vector operators.
    BvBin(BvBinOp),
    /// `concat`
    BvConcat,
    /// `((_ extract high low) arg)`
    BvExtract {
        /// High bit index, inclusive.
        high: u32,
        /// Low bit index, inclusive.
        low: u32,
    },
    /// `select`
    Select,
    /// `store`
    Store,
    /// `str.len`
    StrLen,
    /// `str.++`
    StrConcat,
    /// `str.at`
    StrAt,
    /// `str.contains`
    StrContains,
    /// `str.substr`
    StrSubstr,
    /// `str.indexof`
    StrIndexOf,
    /// `str.<` (`strict`) or `str.<=`
    StrOrder {
        /// `true` for `str.<`, `false` for `str.<=`.
        strict: bool,
    },
    /// `str.to_code`
    StrToCode,
    /// `str.from_code`
    StrFromCode,
}

/// Combine the operands of a fixed-arity operator.
///
/// `operands` are the operator's argument term ids (needed by the one arm
/// that reports a sub-term as undefined) and `values` are their evaluated
/// values, in the same order. The caller only reaches this function when
/// *every* operand evaluated to a `Value`; failures are resolved by the
/// driver before it gets here.
pub(super) fn combine_eager(kind: &EagerKind, operands: &[TermId], values: &[Value]) -> EvalResult {
    match (kind, values) {
        // ======== Boolean ========
        (EagerKind::Not, [a]) => match a {
            Value::Bool(b) => EvalResult::Ok(Value::Bool(!b)),
            _ => EvalResult::Error("Not: expected bool".to_string()),
        },
        (EagerKind::Xor, [a, b]) => match (a, b) {
            (Value::Bool(x), Value::Bool(y)) => EvalResult::Ok(Value::Bool(x ^ y)),
            _ => EvalResult::Error("Xor: expected bools".to_string()),
        },
        (EagerKind::Implies, [a, b]) => match (a, b) {
            (Value::Bool(x), Value::Bool(y)) => EvalResult::Ok(Value::Bool(!x || *y)),
            _ => EvalResult::Error("Implies: expected bools".to_string()),
        },
        (EagerKind::Eq, [a, b]) => EvalResult::Ok(Value::Bool(a == b)),

        // ======== Arithmetic ========
        (EagerKind::Sub, [a, b]) => match (a, b) {
            (Value::Int(x), Value::Int(y)) => match (*x).checked_sub(*y) {
                Some(d) => EvalResult::Ok(Value::Int(d)),
                None => arith_overflow("Sub"),
            },
            _ => match (a.as_rational(), b.as_rational()) {
                (Some(r1), Some(r2)) => match r1.checked_sub(&r2) {
                    Some(d) => from_rational(d),
                    None => arith_overflow("Sub"),
                },
                _ => EvalResult::Error("Sub: expected numbers".to_string()),
            },
        },
        (EagerKind::Div { int_sorted }, [a, b]) => combine_div(*int_sorted, a, b),
        (EagerKind::Mod, [a, b]) => combine_mod(a, b),
        // Negation is the one arithmetic operator that overflows on a *single*
        // operand: `-i64::MIN` has no `i64`. The rational arm negates the
        // numerator of an already-reduced ratio, which keeps it reduced and
        // its denominator positive, so no re-reduction is needed; the result
        // goes through `from_rational` like every other arithmetic arm, so
        // `(- 1.0)` reports `Int(-1)` rather than being the one operator that
        // leaves an integral rational un-normalized.
        (EagerKind::Neg, [a]) => match a {
            Value::Int(n) => match (*n).checked_neg() {
                Some(v) => EvalResult::Ok(Value::Int(v)),
                None => arith_overflow("Neg"),
            },
            Value::Rational(r) => match (*r.numer()).checked_neg() {
                Some(numer) => from_rational(Rational64::new_raw(numer, *r.denom())),
                None => arith_overflow("Neg"),
            },
            _ => EvalResult::Error("Neg: expected number".to_string()),
        },
        (EagerKind::Lt, [a, b]) => match (a.as_rational(), b.as_rational()) {
            (Some(r1), Some(r2)) => EvalResult::Ok(Value::Bool(r1 < r2)),
            _ => EvalResult::Error("Lt: expected numbers".to_string()),
        },
        (EagerKind::Le, [a, b]) => match (a.as_rational(), b.as_rational()) {
            (Some(r1), Some(r2)) => EvalResult::Ok(Value::Bool(r1 <= r2)),
            _ => EvalResult::Error("Le: expected numbers".to_string()),
        },

        // ======== Bitvectors ========
        (EagerKind::BvNot, [a]) => match a {
            Value::BitVec(w, v) => EvalResult::Ok(Value::BitVec(*w, !v & bv_mask(*w))),
            _ => EvalResult::Error("BvNot: expected bitvector".to_string()),
        },
        (EagerKind::BvExtract { high, low }, [a]) => match a {
            Value::BitVec(_, v) => {
                if high < low {
                    return EvalResult::Error("BvExtract: high < low".to_string());
                }
                // `high - low` cannot underflow after the check above, but the
                // inclusive `+ 1` overflows u32 for the widest possible range.
                let Some(width) = (high - low).checked_add(1) else {
                    return EvalResult::Error("BvExtract: result width overflows u32".to_string());
                };
                let shifted = v.wrapping_shr(*low);
                EvalResult::Ok(Value::BitVec(width, shifted & bv_mask(width)))
            }
            _ => EvalResult::Error("BvExtract: expected bitvector".to_string()),
        },
        (EagerKind::BvBin(op), [a, b]) => combine_bv_binary(*op, a, b),
        (EagerKind::BvConcat, [a, b]) => match (a, b) {
            // The combined width must still fit in the 64-bit magnitude
            // `Value::BitVec` represents; wider results surface an explicit
            // error rather than a silently truncated value.
            (Value::BitVec(w1, v1), Value::BitVec(w2, v2)) => match w1.checked_add(*w2) {
                Some(result_width) if result_width <= 64 => {
                    let combined = v1.wrapping_shl(*w2) | v2;
                    EvalResult::Ok(Value::BitVec(result_width, combined))
                }
                Some(result_width) => EvalResult::Error(format!(
                    "BvConcat: result width {result_width} exceeds the 64-bit \
                     magnitude ModelEvaluator can represent"
                )),
                None => EvalResult::Error("BvConcat: result width overflows u32".to_string()),
            },
            _ => EvalResult::Error("BvConcat: expected bitvectors".to_string()),
        },

        // ======== Arrays ========
        //
        // `select` looks up the index in the array's exception list (most
        // recently `store`d entry wins), falling back to the array's default
        // value.
        (EagerKind::Select, [array, index]) => match array {
            Value::Array(default, excs) => {
                for (k, v) in excs.iter().rev() {
                    if k == index {
                        return EvalResult::Ok(v.clone());
                    }
                }
                EvalResult::Ok((**default).clone())
            }
            _ => EvalResult::Error("Select: expected array".to_string()),
        },
        // `store` produces a new array value with `(index, value)` appended as
        // the newest exception on top of the evaluated base array – `select`
        // resolves ties by walking the exception list from the end, so this
        // correctly shadows any prior binding for the same index without
        // needing to search-and-replace here.
        (EagerKind::Store, [array, index, value]) => match array {
            Value::Array(default, excs) => {
                let mut excs = excs.clone();
                excs.push((index.clone(), value.clone()));
                EvalResult::Ok(Value::Array(default.clone(), excs))
            }
            _ => EvalResult::Error("Store: expected array".to_string()),
        },

        // ======== Strings ========
        (EagerKind::StrLen, [a]) => match a {
            // SMT-LIB counts Unicode codepoints, not UTF-8 bytes.
            Value::String(s) => match i64::try_from(s.chars().count()) {
                Ok(len) => EvalResult::Ok(Value::Int(len)),
                Err(_) => arith_overflow("StrLen"),
            },
            _ => EvalResult::Error("StrLen: expected string".to_string()),
        },
        (EagerKind::StrConcat, [a, b]) => match (a, b) {
            (Value::String(s1), Value::String(s2)) => {
                EvalResult::Ok(Value::String(s1.clone() + s2.as_str()))
            }
            _ => EvalResult::Error("StrConcat: expected strings".to_string()),
        },
        (EagerKind::StrAt, [s, i]) => match (s, i) {
            // The single-codepoint substring at codepoint offset `i`, or `""`
            // if `i` is out of `[0, |s|)`. An offset that does not even fit
            // `usize` is out of range by definition, so it takes the same
            // branch instead of being truncated into a valid-looking one.
            (Value::String(s), Value::Int(idx)) => match usize::try_from(*idx) {
                Ok(idx) => match s.chars().nth(idx) {
                    Some(c) => EvalResult::Ok(Value::String(c.to_string())),
                    None => EvalResult::Ok(Value::String(String::new())),
                },
                Err(_) => EvalResult::Ok(Value::String(String::new())),
            },
            _ => EvalResult::Error("StrAt: expected (string, int)".to_string()),
        },
        (EagerKind::StrContains, [s, sub]) => match (s, sub) {
            (Value::String(h), Value::String(n)) => EvalResult::Ok(Value::Bool(h.contains(n))),
            _ => EvalResult::Error("StrContains: expected strings".to_string()),
        },
        (EagerKind::StrSubstr, [s, start, len]) => combine_str_substr(s, start, len),
        (EagerKind::StrIndexOf, [h, n, start]) => combine_str_indexof(h, n, start),
        (EagerKind::StrOrder { strict }, [lhs, rhs]) => match (lhs, rhs) {
            // The order is the lexicographic extension of the numerical order
            // on code points; `crate::ast::str_fold` holds the single
            // definition of it, so the model evaluator, the term builders and
            // the string theory's ground evaluator cannot disagree.
            (Value::String(a), Value::String(b)) => {
                let holds = if *strict {
                    str_fold::str_lt(a, b)
                } else {
                    str_fold::str_le(a, b)
                };
                EvalResult::Ok(Value::Bool(holds))
            }
            _ => EvalResult::Error("str.< / str.<=: expected strings".to_string()),
        },
        (EagerKind::StrToCode, [s]) => match s {
            // Every result is either `-1` or a code point bounded by
            // `MAX_CODE_POINT`, so it always fits `i64`.
            Value::String(value) => match str_fold::str_to_code(value).to_i64() {
                Some(code) => EvalResult::Ok(Value::Int(code)),
                None => EvalResult::Error("str.to_code: code point out of range".to_string()),
            },
            _ => EvalResult::Error("str.to_code: expected a string".to_string()),
        },
        (EagerKind::StrFromCode, [n]) => match n {
            Value::Int(code) => match str_fold::str_from_code(&BigInt::from(*code)) {
                str_fold::FromCode::Char(c) => {
                    let mut text = String::new();
                    text.push(c);
                    EvalResult::Ok(Value::String(text))
                }
                str_fold::FromCode::Empty => EvalResult::Ok(Value::String(String::new())),
                // A surrogate code point is inside the alphabet but not
                // representable as a Rust `char`; rather than fabricate `""`
                // (which has the wrong length) report the *operand* term as
                // undefined, so the caller keeps an honest `unknown`.
                str_fold::FromCode::Unrepresentable => match operands.first() {
                    Some(operand) => EvalResult::Undefined(*operand),
                    None => {
                        EvalResult::Error("internal: str.from_code without an operand".to_string())
                    }
                },
            },
            _ => EvalResult::Error("str.from_code: expected an integer".to_string()),
        },

        // The driver builds each frame with the arity its operator declares
        // (see `Frame::unary` / `binary` / `ternary`), so a mismatch here is an
        // internal inconsistency rather than anything a caller can provoke.
        _ => EvalResult::Error(format!("internal: {} operands for {kind:?}", values.len())),
    }
}

/// Evaluate a division node from its operand values.
///
/// The shared [`crate::ast::TermKind::Div`] carries SMT-LIB semantics chosen by
/// the operand sort: Int operands mean Euclidean integer division `(div a b)`
/// (`a = b*q + r`, `0 <= r < |b|`, via [`i64::div_euclid`], e.g. `(div -7 2) =
/// -4`); Real operands mean exact rational division. `int_sorted` is decided by
/// the *sort* of the numerator term – not the evaluated value's runtime shape –
/// because a Real-sorted quotient such as `(/ 3.0 2.0)` can have
/// integer-valued operands yet must not truncate.
fn combine_div(int_sorted: bool, a: &Value, b: &Value) -> EvalResult {
    let (Some(r1), Some(r2)) = (a.as_rational(), b.as_rational()) else {
        return EvalResult::Error("Div: expected numbers".to_string());
    };
    if r2 == Rational64::from_integer(0) {
        // Division by zero is total-but-unspecified in SMT-LIB; the
        // evaluator cannot invent the value.
        return EvalResult::Error("Division by zero".to_string());
    }
    if int_sorted {
        if !r1.is_integer() || !r2.is_integer() {
            return EvalResult::Error(
                "Div: integer division requires integer operands".to_string(),
            );
        }
        // `div_euclid` panics on the one overflowing case
        // (`i64::MIN.div_euclid(-1)`); report it honestly instead.
        return match r1.numer().checked_div_euclid(*r2.numer()) {
            Some(q) => EvalResult::Ok(Value::Int(q)),
            None => EvalResult::Error("Div: result overflows i64".to_string()),
        };
    }
    // Exact rational division cross-multiplies, so a quotient of two
    // representable ratios need not itself be representable.
    match r1.checked_div(&r2) {
        Some(q) => from_rational(q),
        None => arith_overflow("Div"),
    }
}

/// Evaluate an integer modulo node from its operand values.
///
/// `mod` is integer-only in SMT-LIB and always denotes the Euclidean
/// remainder: `(mod a b) = a - b*(div a b)` with `0 <= (mod a b) < |b|`
/// (via [`i64::rem_euclid`], e.g. `(mod -7 2) = 1`). Modulo by zero is
/// unspecified, so the evaluator surfaces an explicit error rather than a
/// fabricated value.
fn combine_mod(a: &Value, b: &Value) -> EvalResult {
    let (Some(r1), Some(r2)) = (a.as_rational(), b.as_rational()) else {
        return EvalResult::Error("Mod: expected numbers".to_string());
    };
    if !r1.is_integer() || !r2.is_integer() {
        return EvalResult::Error("Mod: expected integer operands".to_string());
    }
    let divisor = *r2.numer();
    if divisor == 0 {
        return EvalResult::Error("Modulo by zero".to_string());
    }
    // `rem_euclid` panics on the one overflowing case
    // (`i64::MIN.rem_euclid(-1)`) in both debug and release; report it
    // honestly instead, mirroring `combine_div`'s `checked_div_euclid` arm.
    match r1.numer().checked_rem_euclid(divisor) {
        Some(r) => EvalResult::Ok(Value::Int(r)),
        None => EvalResult::Error("Mod: result overflows i64".to_string()),
    }
}

/// The binary bit-vector operators, which all share the same operand shape
/// (two same-width bit-vectors) and therefore the same failure messages.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum BvBinOp {
    /// `bvand`
    And,
    /// `bvor`
    Or,
    /// `bvxor`
    Xor,
    /// `bvadd`
    Add,
    /// `bvsub`
    Sub,
    /// `bvmul`
    Mul,
    /// `bvudiv`
    Udiv,
    /// `bvsdiv`
    Sdiv,
    /// `bvurem`
    Urem,
    /// `bvsrem`
    Srem,
    /// `bvshl`
    Shl,
    /// `bvlshr`
    Lshr,
    /// `bvashr`
    Ashr,
    /// `bvult`
    Ult,
    /// `bvule`
    Ule,
    /// `bvslt`
    Slt,
    /// `bvsle`
    Sle,
}

impl BvBinOp {
    /// The operator name used in this operator's error messages.
    fn name(self) -> &'static str {
        match self {
            BvBinOp::And => "BvAnd",
            BvBinOp::Or => "BvOr",
            BvBinOp::Xor => "BvXor",
            BvBinOp::Add => "BvAdd",
            BvBinOp::Sub => "BvSub",
            BvBinOp::Mul => "BvMul",
            BvBinOp::Udiv => "BvUdiv",
            BvBinOp::Sdiv => "BvSdiv",
            BvBinOp::Urem => "BvUrem",
            BvBinOp::Srem => "BvSrem",
            BvBinOp::Shl => "BvShl",
            BvBinOp::Lshr => "BvLshr",
            BvBinOp::Ashr => "BvAshr",
            BvBinOp::Ult => "BvUlt",
            BvBinOp::Ule => "BvUle",
            BvBinOp::Slt => "BvSlt",
            BvBinOp::Sle => "BvSle",
        }
    }
}

/// Combine a binary bit-vector operator's operand values.
///
/// SMT-LIB's `FixedSizeBitVectors` theory is total, so the division,
/// remainder and shift operators all have a defined answer for the cases a
/// machine instruction would trap on; those answers are spelled out per arm.
fn combine_bv_binary(op: BvBinOp, a: &Value, b: &Value) -> EvalResult {
    let (w, v1, v2) = match bv_operands(a, b, op.name()) {
        Ok(operands) => operands,
        Err(e) => return e,
    };
    let mask = bv_mask(w);
    let value = match op {
        BvBinOp::And => v1 & v2,
        BvBinOp::Or => v1 | v2,
        BvBinOp::Xor => v1 ^ v2,
        BvBinOp::Add => v1.wrapping_add(v2) & mask,
        BvBinOp::Sub => v1.wrapping_sub(v2) & mask,
        BvBinOp::Mul => v1.wrapping_mul(v2) & mask,
        // Division by the all-zero bitvector yields the all-ones bitvector.
        BvBinOp::Udiv => match v1.checked_div(v2) {
            Some(q) => q,
            None => mask,
        },
        // Remainder by the all-zero bitvector yields the dividend unchanged.
        BvBinOp::Urem => match v1.checked_rem(v2) {
            Some(r) => r,
            None => v1,
        },
        // `bvsdiv` is `bvudiv` on absolute values with the sign of the result
        // equal to the XOR of the operand signs; division by zero yields the
        // all-ones bitvector when the dividend is non-negative, or `1` when it
        // is negative.
        BvBinOp::Sdiv => {
            if v2 == 0 {
                if bv_is_negative(w, v1) { 1 } else { mask }
            } else {
                let s_neg = bv_is_negative(w, v1);
                let t_neg = bv_is_negative(w, v2);
                let abs_s = if s_neg { bv_negate(w, v1) } else { v1 };
                let abs_t = if t_neg { bv_negate(w, v2) } else { v2 };
                let uq = abs_s / abs_t;
                if s_neg != t_neg { bv_negate(w, uq) } else { uq }
            }
        }
        // `bvsrem` is `bvurem` on absolute values with the sign of the result
        // equal to the sign of the dividend; remainder by zero yields the
        // dividend unchanged.
        BvBinOp::Srem => {
            if v2 == 0 {
                v1
            } else {
                let s_neg = bv_is_negative(w, v1);
                let abs_s = if s_neg { bv_negate(w, v1) } else { v1 };
                let abs_t = if bv_is_negative(w, v2) {
                    bv_negate(w, v2)
                } else {
                    v2
                };
                let ur = abs_s % abs_t;
                if s_neg { bv_negate(w, ur) } else { ur }
            }
        }
        // Shift amounts at or beyond the (effective) width zero out the whole
        // result, matching `bvshl`/`bvlshr` totality over any shift amount.
        BvBinOp::Shl => {
            let eff = bv_eff_width(w);
            if eff == 0 || v2 >= u64::from(eff) {
                0
            } else {
                v1.wrapping_shl(v2 as u32) & mask
            }
        }
        BvBinOp::Lshr => {
            let eff = bv_eff_width(w);
            if eff == 0 || v2 >= u64::from(eff) {
                0
            } else {
                v1.wrapping_shr(v2 as u32) & mask
            }
        }
        // Arithmetic right shift is sign-filled, so an out-of-range shift
        // saturates toward `-1` for a negative operand and `0` otherwise.
        BvBinOp::Ashr => {
            let eff = bv_eff_width(w);
            let negative = bv_is_negative(w, v1);
            if eff == 0 || v2 >= u64::from(eff) {
                if negative { mask } else { 0 }
            } else {
                let shift = v2 as u32;
                let shifted = v1.wrapping_shr(shift);
                if negative {
                    let fill = mask & !(mask.wrapping_shr(shift));
                    (shifted | fill) & mask
                } else {
                    shifted & mask
                }
            }
        }
        // The comparisons produce a Bool rather than a bitvector.
        BvBinOp::Ult => return EvalResult::Ok(Value::Bool(v1 < v2)),
        BvBinOp::Ule => return EvalResult::Ok(Value::Bool(v1 <= v2)),
        BvBinOp::Slt => {
            return EvalResult::Ok(Value::Bool(
                bv_signed_cmp(w, v1, v2) == core::cmp::Ordering::Less,
            ));
        }
        BvBinOp::Sle => {
            return EvalResult::Ok(Value::Bool(
                bv_signed_cmp(w, v1, v2) != core::cmp::Ordering::Greater,
            ));
        }
    };
    EvalResult::Ok(Value::BitVec(w, value))
}

/// Evaluate `str.substr` (codepoint offsets; out-of-range/negative arguments
/// yield `""` per SMT-LIB's total semantics).
fn combine_str_substr(s: &Value, start: &Value, len: &Value) -> EvalResult {
    let (Value::String(s), Value::Int(st), Value::Int(ln)) = (s, start, len) else {
        return EvalResult::Error("StrSubstr: expected (string, int, int)".to_string());
    };
    let char_count = s.chars().count();
    // An offset or length that does not fit `usize` cannot name any position
    // in a string that does fit memory, so it is out of range rather than
    // something to truncate.
    let (Ok(start_idx), Ok(len)) = (usize::try_from(*st), usize::try_from(*ln)) else {
        return EvalResult::Ok(Value::String(String::new()));
    };
    if start_idx > char_count {
        return EvalResult::Ok(Value::String(String::new()));
    }
    let end_idx = start_idx.saturating_add(len).min(char_count);
    let result: String = s
        .chars()
        .skip(start_idx)
        .take(end_idx - start_idx)
        .collect();
    EvalResult::Ok(Value::String(result))
}

/// Evaluate `str.indexof` (codepoint offsets). Mirrors the SMT-LIB side
/// condition for an empty needle (`indexof(s, "", i) = i` iff `0 <= i <= |s|`,
/// else `-1`) and converts the Rust byte-offset match position back to a
/// codepoint offset for a non-empty needle.
fn combine_str_indexof(haystack: &Value, needle: &Value, start: &Value) -> EvalResult {
    let (Value::String(h), Value::String(n), Value::Int(st)) = (haystack, needle, start) else {
        return EvalResult::Error("StrIndexOf: expected (string, string, int)".to_string());
    };
    // Same reasoning as `combine_str_substr`: a negative offset, or one too
    // large for `usize`, cannot name a position in `h`.
    let Ok(start_idx) = usize::try_from(*st) else {
        return EvalResult::Ok(Value::Int(-1));
    };
    let h_char_count = h.chars().count();
    if n.is_empty() {
        return EvalResult::Ok(Value::Int(if start_idx <= h_char_count { *st } else { -1 }));
    }
    if start_idx > h_char_count {
        return EvalResult::Ok(Value::Int(-1));
    }
    let byte_start = h.char_indices().nth(start_idx).map_or(h.len(), |(b, _)| b);
    match h[byte_start..].find(n.as_str()) {
        Some(byte_pos) => {
            let char_pos = h[..byte_start + byte_pos].chars().count();
            match i64::try_from(char_pos) {
                Ok(pos) => EvalResult::Ok(Value::Int(pos)),
                Err(_) => arith_overflow("StrIndexOf"),
            }
        }
        None => EvalResult::Ok(Value::Int(-1)),
    }
}

/// Combine the operand values of `distinct`: `true` iff no two of them are
/// equal.
pub(super) fn combine_distinct(values: &[Value]) -> EvalResult {
    for i in 0..values.len() {
        for j in (i + 1)..values.len() {
            if values[i] == values[j] {
                return EvalResult::Ok(Value::Bool(false));
            }
        }
    }
    EvalResult::Ok(Value::Bool(true))
}

/// Finish an n-ary `+` / `*` from its running accumulator.
pub(super) fn finish_arith(acc: Rational64) -> EvalResult {
    from_rational(acc)
}
