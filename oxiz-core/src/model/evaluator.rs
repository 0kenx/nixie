//! Model Evaluator
//!
//! Evaluates terms under a given model assignment.

use super::{Model, Value};
use crate::ast::{TermId, TermKind, TermManager};
use crate::prelude::HashMap;
#[allow(unused_imports)]
use crate::prelude::*;
use num_rational::Rational64;

// ===== Bitvector arithmetic helpers =====
//
// `Value::BitVec` stores a bitvector as `(declared_width: u32, magnitude:
// u64)` — the magnitude is capped at 64 bits regardless of the declared
// width (see the `BitVecConst` arm of `eval_term` for why: a magnitude
// that does not fit `u64` is surfaced as an explicit error rather than
// fabricated). The helpers below encode that representation's
// consequences once, instead of re-deriving them at every BV eval site:
//
// - For `width <= 64` the magnitude is an exact `width`-bit two's
//   complement value, so sign/shift/div-by-zero handling follows the
//   SMT-LIB `FixedSizeBitVectors` theory directly.
// - For `width > 64`, only magnitudes `< 2^64 <= 2^(width-1)` are ever
//   representable, so such values are *always* non-negative in their true
//   `width`-bit interpretation — the "effective width" for sign/shift
//   purposes is therefore capped at 64.

/// Effective width used for masking/sign checks: `Value::BitVec`'s
/// magnitude cannot exceed 64 bits no matter what `width` is declared as.
fn bv_eff_width(width: u32) -> u32 {
    width.min(64)
}

/// The SMT-LIB bitvector modulus mask for `width` bits, capped at the
/// 64-bit magnitude `Value::BitVec` can represent.
fn bv_mask(width: u32) -> u64 {
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

/// Result of evaluation
#[derive(Debug, Clone)]
pub enum EvalResult {
    /// Successful evaluation
    Ok(Value),
    /// Term has no value in model
    Undefined(TermId),
    /// Evaluation error
    Error(String),
}

impl EvalResult {
    /// Check if evaluation succeeded
    pub fn is_ok(&self) -> bool {
        matches!(self, EvalResult::Ok(_))
    }

    /// Get value if successful
    pub fn value(&self) -> Option<&Value> {
        match self {
            EvalResult::Ok(v) => Some(v),
            _ => None,
        }
    }

    /// Unwrap value or panic
    pub fn unwrap(self) -> Value {
        match self {
            EvalResult::Ok(v) => v,
            EvalResult::Undefined(t) => panic!("Term {:?} is undefined", t),
            EvalResult::Error(e) => panic!("Evaluation error: {}", e),
        }
    }
}

/// Cache for evaluated terms
#[derive(Debug, Default)]
pub struct EvalCache {
    cache: HashMap<TermId, Value>,
}

impl EvalCache {
    /// Create a new cache
    pub fn new() -> Self {
        Self::default()
    }

    /// Get cached value
    pub fn get(&self, term: TermId) -> Option<&Value> {
        self.cache.get(&term)
    }

    /// Insert value into cache
    pub fn insert(&mut self, term: TermId, value: Value) {
        self.cache.insert(term, value);
    }

    /// Clear the cache
    pub fn clear(&mut self) {
        self.cache.clear();
    }

    /// Number of cached entries
    pub fn len(&self) -> usize {
        self.cache.len()
    }

    /// Check if cache is empty
    pub fn is_empty(&self) -> bool {
        self.cache.is_empty()
    }
}

/// Model evaluator with caching
#[derive(Debug)]
pub struct ModelEvaluator<'a> {
    model: &'a Model,
    cache: EvalCache,
    use_cache: bool,
}

impl<'a> ModelEvaluator<'a> {
    /// Create a new evaluator
    pub fn new(model: &'a Model) -> Self {
        Self {
            model,
            cache: EvalCache::new(),
            use_cache: true,
        }
    }

    /// Create evaluator without caching
    pub fn without_cache(model: &'a Model) -> Self {
        Self {
            model,
            cache: EvalCache::new(),
            use_cache: false,
        }
    }

    /// Evaluate a term
    pub fn eval(&mut self, term: TermId, manager: &TermManager) -> EvalResult {
        // Check cache first
        if self.use_cache
            && let Some(v) = self.cache.get(term)
        {
            return EvalResult::Ok(v.clone());
        }

        // Check model assignment
        if let Some(v) = self.model.get(term) {
            if self.use_cache {
                self.cache.insert(term, v.clone());
            }
            return EvalResult::Ok(v.clone());
        }

        // Evaluate based on term structure
        let result = self.eval_term(term, manager);

        // Cache result
        if self.use_cache
            && let EvalResult::Ok(ref v) = result
        {
            self.cache.insert(term, v.clone());
        }

        result
    }

    /// Internal evaluation
    fn eval_term(&mut self, term: TermId, manager: &TermManager) -> EvalResult {
        let t = match manager.get(term) {
            Some(t) => t,
            None => return EvalResult::Error(format!("Unknown term: {:?}", term)),
        };

        match &t.kind {
            // Constants
            TermKind::True => EvalResult::Ok(Value::Bool(true)),
            TermKind::False => EvalResult::Ok(Value::Bool(false)),
            TermKind::IntConst(n) => {
                // Convert BigInt to i64, without silently truncating out-of-range
                // values to 0. `Value::Int` is a fixed-width i64 representation
                // (see model/mod.rs); a BigInt that does not fit cannot be
                // represented faithfully, so surface an explicit error instead
                // of fabricating a wrong value.
                match i64::try_from(n) {
                    Ok(val) => EvalResult::Ok(Value::Int(val)),
                    Err(_) => EvalResult::Error(format!(
                        "IntConst {n} does not fit in i64; wide integer model \
                         values are not yet representable by ModelEvaluator"
                    )),
                }
            }
            TermKind::RealConst(r) => EvalResult::Ok(Value::Rational(*r)),
            TermKind::StringLit(s) => EvalResult::Ok(Value::String(s.clone())),
            TermKind::BitVecConst { value, width } => {
                // Convert BigInt to u64, without silently truncating out-of-range
                // values to 0. `Value::BitVec` stores its payload as a u64
                // magnitude alongside a (possibly >64) declared width — see
                // `Value`'s Display impl in model/mod.rs, which zero-extends
                // the u64 magnitude out to `width` bits. That representation
                // is exact as long as the constant's magnitude fits in u64;
                // when it does not (e.g. a >64-bit constant whose value
                // itself exceeds u64::MAX), surface an explicit error instead
                // of fabricating a wrong (truncated-to-something-else) value.
                match u64::try_from(value) {
                    Ok(val) => EvalResult::Ok(Value::BitVec(*width, val)),
                    Err(_) => EvalResult::Error(format!(
                        "BitVecConst {value} (width {width}) does not fit in u64; \
                         wide bitvector model values with magnitude beyond u64::MAX \
                         are not yet representable by ModelEvaluator"
                    )),
                }
            }

            // Variables - look up in model
            TermKind::Var(_) => match self.model.get(term) {
                Some(v) => EvalResult::Ok(v.clone()),
                None => EvalResult::Undefined(term),
            },

            // Boolean operations
            TermKind::Not(inner) => match self.eval(*inner, manager) {
                EvalResult::Ok(Value::Bool(b)) => EvalResult::Ok(Value::Bool(!b)),
                EvalResult::Ok(_) => EvalResult::Error("Not: expected bool".to_string()),
                e => e,
            },
            TermKind::And(args) => self.eval_and(args.as_slice(), manager),
            TermKind::Or(args) => self.eval_or(args.as_slice(), manager),
            TermKind::Xor(a, b) => match (self.eval(*a, manager), self.eval(*b, manager)) {
                (EvalResult::Ok(Value::Bool(x)), EvalResult::Ok(Value::Bool(y))) => {
                    EvalResult::Ok(Value::Bool(x ^ y))
                }
                (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                    EvalResult::Error("Xor: expected bools".to_string())
                }
                (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
                (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
            },
            TermKind::Implies(a, b) => match (self.eval(*a, manager), self.eval(*b, manager)) {
                (EvalResult::Ok(Value::Bool(x)), EvalResult::Ok(Value::Bool(y))) => {
                    EvalResult::Ok(Value::Bool(!x || y))
                }
                (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                    EvalResult::Error("Implies: expected bools".to_string())
                }
                (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
                (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
            },
            TermKind::Ite(cond, then_branch, else_branch) => match self.eval(*cond, manager) {
                EvalResult::Ok(Value::Bool(true)) => self.eval(*then_branch, manager),
                EvalResult::Ok(Value::Bool(false)) => self.eval(*else_branch, manager),
                EvalResult::Ok(_) => EvalResult::Error("Ite: condition must be bool".to_string()),
                e => e,
            },

            // Equality
            TermKind::Eq(a, b) => match (self.eval(*a, manager), self.eval(*b, manager)) {
                (EvalResult::Ok(v1), EvalResult::Ok(v2)) => EvalResult::Ok(Value::Bool(v1 == v2)),
                (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
                (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
            },
            TermKind::Distinct(args) => self.eval_distinct(args.as_slice(), manager),

            // Arithmetic
            TermKind::Add(args) => self.eval_add(args.as_slice(), manager),
            TermKind::Sub(a, b) => self.eval_sub(*a, *b, manager),
            TermKind::Mul(args) => self.eval_mul(args.as_slice(), manager),
            TermKind::Div(a, b) => self.eval_div(*a, *b, manager),
            TermKind::Mod(a, b) => self.eval_mod(*a, *b, manager),
            TermKind::Neg(a) => self.eval_neg(*a, manager),
            TermKind::Lt(a, b) => self.eval_lt(*a, *b, manager),
            TermKind::Le(a, b) => self.eval_le(*a, *b, manager),
            TermKind::Gt(a, b) => self.eval_lt(*b, *a, manager),
            TermKind::Ge(a, b) => self.eval_le(*b, *a, manager),

            // Bitvector operations
            TermKind::BvNot(a) => self.eval_bvnot(*a, manager),
            TermKind::BvAnd(a, b) => self.eval_bvand(*a, *b, manager),
            TermKind::BvOr(a, b) => self.eval_bvor(*a, *b, manager),
            TermKind::BvXor(a, b) => self.eval_bvxor(*a, *b, manager),
            TermKind::BvAdd(a, b) => self.eval_bvadd(*a, *b, manager),
            TermKind::BvSub(a, b) => self.eval_bvsub(*a, *b, manager),
            TermKind::BvMul(a, b) => self.eval_bvmul(*a, *b, manager),
            TermKind::BvUdiv(a, b) => self.eval_bvudiv(*a, *b, manager),
            TermKind::BvSdiv(a, b) => self.eval_bvsdiv(*a, *b, manager),
            TermKind::BvUrem(a, b) => self.eval_bvurem(*a, *b, manager),
            TermKind::BvSrem(a, b) => self.eval_bvsrem(*a, *b, manager),
            TermKind::BvShl(a, b) => self.eval_bvshl(*a, *b, manager),
            TermKind::BvLshr(a, b) => self.eval_bvlshr(*a, *b, manager),
            TermKind::BvAshr(a, b) => self.eval_bvashr(*a, *b, manager),
            TermKind::BvUlt(a, b) => self.eval_bvult(*a, *b, manager),
            TermKind::BvUle(a, b) => self.eval_bvule(*a, *b, manager),
            TermKind::BvSlt(a, b) => self.eval_bvslt(*a, *b, manager),
            TermKind::BvSle(a, b) => self.eval_bvsle(*a, *b, manager),
            TermKind::BvConcat(a, b) => self.eval_bvconcat(*a, *b, manager),
            TermKind::BvExtract { high, low, arg } => {
                self.eval_bvextract(*high, *low, *arg, manager)
            }

            // Array operations
            TermKind::Select(array, index) => self.eval_select(*array, *index, manager),
            TermKind::Store(array, index, value) => {
                self.eval_store(*array, *index, *value, manager)
            }

            // String operations
            TermKind::StrLen(arg) => self.eval_strlen(*arg, manager),
            TermKind::StrConcat(a, b) => self.eval_strconcat(*a, *b, manager),
            TermKind::StrAt(s, i) => self.eval_strat(*s, *i, manager),
            TermKind::StrContains(s, sub) => self.eval_strcontains(*s, *sub, manager),
            TermKind::StrSubstr(s, i, n) => self.eval_strsubstr(*s, *i, *n, manager),
            TermKind::StrIndexOf(s, sub, offset) => {
                self.eval_strindexof(*s, *sub, *offset, manager)
            }

            // Unhandled - return undefined for now
            _ => EvalResult::Undefined(term),
        }
    }

    fn eval_and(&mut self, args: &[TermId], manager: &TermManager) -> EvalResult {
        for arg in args {
            match self.eval(*arg, manager) {
                EvalResult::Ok(Value::Bool(false)) => return EvalResult::Ok(Value::Bool(false)),
                EvalResult::Ok(Value::Bool(true)) => continue,
                EvalResult::Ok(_) => return EvalResult::Error("And: expected bool".to_string()),
                e => return e,
            }
        }
        EvalResult::Ok(Value::Bool(true))
    }

    fn eval_or(&mut self, args: &[TermId], manager: &TermManager) -> EvalResult {
        for arg in args {
            match self.eval(*arg, manager) {
                EvalResult::Ok(Value::Bool(true)) => return EvalResult::Ok(Value::Bool(true)),
                EvalResult::Ok(Value::Bool(false)) => continue,
                EvalResult::Ok(_) => return EvalResult::Error("Or: expected bool".to_string()),
                e => return e,
            }
        }
        EvalResult::Ok(Value::Bool(false))
    }

    fn eval_distinct(&mut self, args: &[TermId], manager: &TermManager) -> EvalResult {
        let mut values = Vec::with_capacity(args.len());
        for arg in args {
            match self.eval(*arg, manager) {
                EvalResult::Ok(v) => values.push(v),
                e => return e,
            }
        }

        for i in 0..values.len() {
            for j in (i + 1)..values.len() {
                if values[i] == values[j] {
                    return EvalResult::Ok(Value::Bool(false));
                }
            }
        }
        EvalResult::Ok(Value::Bool(true))
    }

    fn eval_add(&mut self, args: &[TermId], manager: &TermManager) -> EvalResult {
        let mut sum = Rational64::from_integer(0);
        for arg in args {
            match self.eval(*arg, manager) {
                EvalResult::Ok(Value::Int(n)) => sum += Rational64::from_integer(n),
                EvalResult::Ok(Value::Rational(r)) => sum += r,
                EvalResult::Ok(_) => return EvalResult::Error("Add: expected number".to_string()),
                e => return e,
            }
        }
        if *sum.denom() == 1 {
            EvalResult::Ok(Value::Int(*sum.numer()))
        } else {
            EvalResult::Ok(Value::Rational(sum))
        }
    }

    fn eval_sub(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(Value::Int(x)), EvalResult::Ok(Value::Int(y))) => {
                EvalResult::Ok(Value::Int(x - y))
            }
            (EvalResult::Ok(v1), EvalResult::Ok(v2)) => {
                match (v1.as_rational(), v2.as_rational()) {
                    (Some(r1), Some(r2)) => {
                        let r = r1 - r2;
                        if *r.denom() == 1 {
                            EvalResult::Ok(Value::Int(*r.numer()))
                        } else {
                            EvalResult::Ok(Value::Rational(r))
                        }
                    }
                    _ => EvalResult::Error("Sub: expected numbers".to_string()),
                }
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    fn eval_mul(&mut self, args: &[TermId], manager: &TermManager) -> EvalResult {
        let mut product = Rational64::from_integer(1);
        for arg in args {
            match self.eval(*arg, manager) {
                EvalResult::Ok(Value::Int(n)) => product *= Rational64::from_integer(n),
                EvalResult::Ok(Value::Rational(r)) => product *= r,
                EvalResult::Ok(_) => return EvalResult::Error("Mul: expected number".to_string()),
                e => return e,
            }
        }
        if *product.denom() == 1 {
            EvalResult::Ok(Value::Int(*product.numer()))
        } else {
            EvalResult::Ok(Value::Rational(product))
        }
    }

    /// Evaluate a division node.
    ///
    /// The shared [`TermKind::Div`] carries SMT-LIB semantics chosen by the
    /// operand sort: Int operands mean Euclidean integer division `(div a b)`
    /// (`a = b*q + r`, `0 <= r < |b|`, via [`i64::div_euclid`], e.g.
    /// `(div -7 2) = -4`); Real operands mean exact rational division. The
    /// dispatch keys off the *sort* of the numerator term — not the evaluated
    /// value's runtime shape — because a Real-sorted quotient such as
    /// `(/ 3.0 2.0)` can have integer-valued operands yet must not truncate.
    fn eval_div(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        let int_sorted = manager
            .get(a)
            .and_then(|t| manager.sorts.get(t.sort))
            .is_some_and(|s| s.is_int());
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(v1), EvalResult::Ok(v2)) => {
                match (v1.as_rational(), v2.as_rational()) {
                    (Some(r1), Some(r2)) => {
                        if r2 == Rational64::from_integer(0) {
                            // Division by zero is total-but-unspecified in
                            // SMT-LIB; the evaluator cannot invent the value.
                            EvalResult::Error("Division by zero".to_string())
                        } else if int_sorted {
                            if !r1.is_integer() || !r2.is_integer() {
                                return EvalResult::Error(
                                    "Div: integer division requires integer operands".to_string(),
                                );
                            }
                            // `div_euclid` panics on the one overflowing
                            // case (`i64::MIN.div_euclid(-1)`); report it
                            // honestly instead.
                            match r1.numer().checked_div_euclid(*r2.numer()) {
                                Some(q) => EvalResult::Ok(Value::Int(q)),
                                None => EvalResult::Error("Div: result overflows i64".to_string()),
                            }
                        } else {
                            let r = r1 / r2;
                            if *r.denom() == 1 {
                                EvalResult::Ok(Value::Int(*r.numer()))
                            } else {
                                EvalResult::Ok(Value::Rational(r))
                            }
                        }
                    }
                    _ => EvalResult::Error("Div: expected numbers".to_string()),
                }
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Evaluate an integer modulo node.
    ///
    /// `mod` is integer-only in SMT-LIB and always denotes the Euclidean
    /// remainder: `(mod a b) = a - b*(div a b)` with `0 <= (mod a b) < |b|`
    /// (via [`i64::rem_euclid`], e.g. `(mod -7 2) = 1`). Modulo by zero is
    /// unspecified, so the evaluator surfaces an explicit error rather than a
    /// fabricated value.
    fn eval_mod(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(v1), EvalResult::Ok(v2)) => {
                match (v1.as_rational(), v2.as_rational()) {
                    (Some(r1), Some(r2)) => {
                        if !r1.is_integer() || !r2.is_integer() {
                            return EvalResult::Error("Mod: expected integer operands".to_string());
                        }
                        let divisor = *r2.numer();
                        if divisor == 0 {
                            EvalResult::Error("Modulo by zero".to_string())
                        } else {
                            // `rem_euclid` panics on the one overflowing case
                            // (`i64::MIN.rem_euclid(-1)`) in both debug and
                            // release; report it honestly instead, mirroring
                            // `eval_div`'s `checked_div_euclid` arm.
                            match r1.numer().checked_rem_euclid(divisor) {
                                Some(r) => EvalResult::Ok(Value::Int(r)),
                                None => EvalResult::Error("Mod: result overflows i64".to_string()),
                            }
                        }
                    }
                    _ => EvalResult::Error("Mod: expected numbers".to_string()),
                }
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    fn eval_neg(&mut self, a: TermId, manager: &TermManager) -> EvalResult {
        match self.eval(a, manager) {
            EvalResult::Ok(Value::Int(n)) => EvalResult::Ok(Value::Int(-n)),
            EvalResult::Ok(Value::Rational(r)) => EvalResult::Ok(Value::Rational(-r)),
            EvalResult::Ok(_) => EvalResult::Error("Neg: expected number".to_string()),
            e => e,
        }
    }

    fn eval_lt(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(v1), EvalResult::Ok(v2)) => {
                match (v1.as_rational(), v2.as_rational()) {
                    (Some(r1), Some(r2)) => EvalResult::Ok(Value::Bool(r1 < r2)),
                    _ => EvalResult::Error("Lt: expected numbers".to_string()),
                }
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    fn eval_le(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(v1), EvalResult::Ok(v2)) => {
                match (v1.as_rational(), v2.as_rational()) {
                    (Some(r1), Some(r2)) => EvalResult::Ok(Value::Bool(r1 <= r2)),
                    _ => EvalResult::Error("Le: expected numbers".to_string()),
                }
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    fn eval_bvnot(&mut self, a: TermId, manager: &TermManager) -> EvalResult {
        match self.eval(a, manager) {
            EvalResult::Ok(Value::BitVec(w, v)) => {
                let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
                EvalResult::Ok(Value::BitVec(w, !v & mask))
            }
            EvalResult::Ok(_) => EvalResult::Error("BvNot: expected bitvector".to_string()),
            e => e,
        }
    }

    fn eval_bvand(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(Value::BitVec(w1, v1)), EvalResult::Ok(Value::BitVec(w2, v2))) => {
                if w1 != w2 {
                    EvalResult::Error("BvAnd: width mismatch".to_string())
                } else {
                    EvalResult::Ok(Value::BitVec(w1, v1 & v2))
                }
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("BvAnd: expected bitvectors".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    fn eval_bvor(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(Value::BitVec(w1, v1)), EvalResult::Ok(Value::BitVec(w2, v2))) => {
                if w1 != w2 {
                    EvalResult::Error("BvOr: width mismatch".to_string())
                } else {
                    EvalResult::Ok(Value::BitVec(w1, v1 | v2))
                }
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("BvOr: expected bitvectors".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    fn eval_bvxor(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(Value::BitVec(w1, v1)), EvalResult::Ok(Value::BitVec(w2, v2))) => {
                if w1 != w2 {
                    EvalResult::Error("BvXor: width mismatch".to_string())
                } else {
                    EvalResult::Ok(Value::BitVec(w1, v1 ^ v2))
                }
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("BvXor: expected bitvectors".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    fn eval_bvadd(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(Value::BitVec(w1, v1)), EvalResult::Ok(Value::BitVec(w2, v2))) => {
                if w1 != w2 {
                    EvalResult::Error("BvAdd: width mismatch".to_string())
                } else {
                    let mask = if w1 >= 64 { u64::MAX } else { (1u64 << w1) - 1 };
                    EvalResult::Ok(Value::BitVec(w1, v1.wrapping_add(v2) & mask))
                }
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("BvAdd: expected bitvectors".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    fn eval_bvsub(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(Value::BitVec(w1, v1)), EvalResult::Ok(Value::BitVec(w2, v2))) => {
                if w1 != w2 {
                    EvalResult::Error("BvSub: width mismatch".to_string())
                } else {
                    let mask = if w1 >= 64 { u64::MAX } else { (1u64 << w1) - 1 };
                    EvalResult::Ok(Value::BitVec(w1, v1.wrapping_sub(v2) & mask))
                }
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("BvSub: expected bitvectors".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    fn eval_bvmul(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(Value::BitVec(w1, v1)), EvalResult::Ok(Value::BitVec(w2, v2))) => {
                if w1 != w2 {
                    EvalResult::Error("BvMul: width mismatch".to_string())
                } else {
                    let mask = if w1 >= 64 { u64::MAX } else { (1u64 << w1) - 1 };
                    EvalResult::Ok(Value::BitVec(w1, v1.wrapping_mul(v2) & mask))
                }
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("BvMul: expected bitvectors".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Evaluate unsigned bitvector division.
    ///
    /// SMT-LIB gives `bvudiv` total semantics: division by the all-zero
    /// bitvector yields the all-ones bitvector rather than being an error.
    fn eval_bvudiv(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(Value::BitVec(w1, v1)), EvalResult::Ok(Value::BitVec(w2, v2))) => {
                if w1 != w2 {
                    EvalResult::Error("BvUdiv: width mismatch".to_string())
                } else {
                    let result = match v1.checked_div(v2) {
                        Some(q) => q,
                        None => bv_mask(w1),
                    };
                    EvalResult::Ok(Value::BitVec(w1, result))
                }
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("BvUdiv: expected bitvectors".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Evaluate unsigned bitvector remainder.
    ///
    /// SMT-LIB total semantics: `bvurem` by the all-zero bitvector yields
    /// the dividend unchanged.
    fn eval_bvurem(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(Value::BitVec(w1, v1)), EvalResult::Ok(Value::BitVec(w2, v2))) => {
                if w1 != w2 {
                    EvalResult::Error("BvUrem: width mismatch".to_string())
                } else {
                    let result = match v1.checked_rem(v2) {
                        Some(r) => r,
                        None => v1,
                    };
                    EvalResult::Ok(Value::BitVec(w1, result))
                }
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("BvUrem: expected bitvectors".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Evaluate signed bitvector division per the SMT-LIB
    /// `FixedSizeBitVectors` theory: `bvsdiv` is `bvudiv` on absolute
    /// values with the sign of the result equal to the XOR of the
    /// operand signs; division by zero yields the all-ones bitvector when
    /// the dividend is non-negative, or `1` when it is negative.
    fn eval_bvsdiv(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(Value::BitVec(w1, v1)), EvalResult::Ok(Value::BitVec(w2, v2))) => {
                if w1 != w2 {
                    return EvalResult::Error("BvSdiv: width mismatch".to_string());
                }
                if v2 == 0 {
                    let result = if bv_is_negative(w1, v1) {
                        1
                    } else {
                        bv_mask(w1)
                    };
                    return EvalResult::Ok(Value::BitVec(w1, result));
                }
                let s_neg = bv_is_negative(w1, v1);
                let t_neg = bv_is_negative(w1, v2);
                let abs_s = if s_neg { bv_negate(w1, v1) } else { v1 };
                let abs_t = if t_neg { bv_negate(w1, v2) } else { v2 };
                let uq = abs_s / abs_t;
                let result = if s_neg != t_neg {
                    bv_negate(w1, uq)
                } else {
                    uq
                };
                EvalResult::Ok(Value::BitVec(w1, result))
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("BvSdiv: expected bitvectors".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Evaluate signed bitvector remainder per the SMT-LIB
    /// `FixedSizeBitVectors` theory: `bvsrem` is `bvurem` on absolute
    /// values with the sign of the result equal to the sign of the
    /// dividend; remainder by zero yields the dividend unchanged.
    fn eval_bvsrem(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(Value::BitVec(w1, v1)), EvalResult::Ok(Value::BitVec(w2, v2))) => {
                if w1 != w2 {
                    return EvalResult::Error("BvSrem: width mismatch".to_string());
                }
                if v2 == 0 {
                    return EvalResult::Ok(Value::BitVec(w1, v1));
                }
                let s_neg = bv_is_negative(w1, v1);
                let abs_s = if s_neg { bv_negate(w1, v1) } else { v1 };
                let abs_t = if bv_is_negative(w1, v2) {
                    bv_negate(w1, v2)
                } else {
                    v2
                };
                let ur = abs_s % abs_t;
                let result = if s_neg { bv_negate(w1, ur) } else { ur };
                EvalResult::Ok(Value::BitVec(w1, result))
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("BvSrem: expected bitvectors".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Evaluate a logical left shift. Shift amounts at or beyond the
    /// (effective) width zero out the whole result, matching SMT-LIB
    /// `bvshl`'s totality over any shift amount.
    fn eval_bvshl(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(Value::BitVec(w1, v1)), EvalResult::Ok(Value::BitVec(w2, v2))) => {
                if w1 != w2 {
                    return EvalResult::Error("BvShl: width mismatch".to_string());
                }
                let eff = bv_eff_width(w1);
                let result = if eff == 0 || v2 >= eff as u64 {
                    0
                } else {
                    v1.wrapping_shl(v2 as u32) & bv_mask(w1)
                };
                EvalResult::Ok(Value::BitVec(w1, result))
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("BvShl: expected bitvectors".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Evaluate a logical right shift (zero-filled).
    fn eval_bvlshr(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(Value::BitVec(w1, v1)), EvalResult::Ok(Value::BitVec(w2, v2))) => {
                if w1 != w2 {
                    return EvalResult::Error("BvLshr: width mismatch".to_string());
                }
                let eff = bv_eff_width(w1);
                let result = if eff == 0 || v2 >= eff as u64 {
                    0
                } else {
                    v1.wrapping_shr(v2 as u32) & bv_mask(w1)
                };
                EvalResult::Ok(Value::BitVec(w1, result))
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("BvLshr: expected bitvectors".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Evaluate an arithmetic right shift (sign-filled).
    fn eval_bvashr(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(Value::BitVec(w1, v1)), EvalResult::Ok(Value::BitVec(w2, v2))) => {
                if w1 != w2 {
                    return EvalResult::Error("BvAshr: width mismatch".to_string());
                }
                let eff = bv_eff_width(w1);
                let mask = bv_mask(w1);
                let negative = bv_is_negative(w1, v1);
                let result = if eff == 0 || v2 >= eff as u64 {
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
                };
                EvalResult::Ok(Value::BitVec(w1, result))
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("BvAshr: expected bitvectors".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Evaluate unsigned bitvector less-than.
    fn eval_bvult(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(Value::BitVec(w1, v1)), EvalResult::Ok(Value::BitVec(w2, v2))) => {
                if w1 != w2 {
                    EvalResult::Error("BvUlt: width mismatch".to_string())
                } else {
                    EvalResult::Ok(Value::Bool(v1 < v2))
                }
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("BvUlt: expected bitvectors".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Evaluate unsigned bitvector less-than-or-equal.
    fn eval_bvule(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(Value::BitVec(w1, v1)), EvalResult::Ok(Value::BitVec(w2, v2))) => {
                if w1 != w2 {
                    EvalResult::Error("BvUle: width mismatch".to_string())
                } else {
                    EvalResult::Ok(Value::Bool(v1 <= v2))
                }
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("BvUle: expected bitvectors".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Evaluate signed bitvector less-than.
    fn eval_bvslt(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(Value::BitVec(w1, v1)), EvalResult::Ok(Value::BitVec(w2, v2))) => {
                if w1 != w2 {
                    EvalResult::Error("BvSlt: width mismatch".to_string())
                } else {
                    EvalResult::Ok(Value::Bool(
                        bv_signed_cmp(w1, v1, v2) == core::cmp::Ordering::Less,
                    ))
                }
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("BvSlt: expected bitvectors".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Evaluate signed bitvector less-than-or-equal.
    fn eval_bvsle(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(Value::BitVec(w1, v1)), EvalResult::Ok(Value::BitVec(w2, v2))) => {
                if w1 != w2 {
                    EvalResult::Error("BvSle: width mismatch".to_string())
                } else {
                    EvalResult::Ok(Value::Bool(
                        bv_signed_cmp(w1, v1, v2) != core::cmp::Ordering::Greater,
                    ))
                }
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("BvSle: expected bitvectors".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Evaluate bitvector concatenation. The combined width must still fit
    /// in the 64-bit magnitude `Value::BitVec` represents; wider results
    /// surface an explicit error rather than a silently truncated value.
    fn eval_bvconcat(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(Value::BitVec(w1, v1)), EvalResult::Ok(Value::BitVec(w2, v2))) => {
                match w1.checked_add(w2) {
                    Some(result_width) if result_width <= 64 => {
                        let combined = v1.wrapping_shl(w2) | v2;
                        EvalResult::Ok(Value::BitVec(result_width, combined))
                    }
                    Some(result_width) => EvalResult::Error(format!(
                        "BvConcat: result width {result_width} exceeds the 64-bit \
                         magnitude ModelEvaluator can represent"
                    )),
                    None => EvalResult::Error("BvConcat: result width overflows u32".to_string()),
                }
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("BvConcat: expected bitvectors".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Evaluate bitvector extraction `((_ extract high low) arg)`.
    fn eval_bvextract(
        &mut self,
        high: u32,
        low: u32,
        arg: TermId,
        manager: &TermManager,
    ) -> EvalResult {
        match self.eval(arg, manager) {
            EvalResult::Ok(Value::BitVec(_, v)) => {
                if high < low {
                    return EvalResult::Error("BvExtract: high < low".to_string());
                }
                let width = high - low + 1;
                let shifted = v.wrapping_shr(low);
                EvalResult::Ok(Value::BitVec(width, shifted & bv_mask(width)))
            }
            EvalResult::Ok(_) => EvalResult::Error("BvExtract: expected bitvector".to_string()),
            e => e,
        }
    }

    /// Evaluate array `select`. Looks up `index` in the array's exception
    /// list (most recently `store`d entry wins), falling back to the
    /// array's default value.
    fn eval_select(&mut self, array: TermId, index: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(array, manager), self.eval(index, manager)) {
            (EvalResult::Ok(Value::Array(default, excs)), EvalResult::Ok(idx)) => {
                for (k, v) in excs.iter().rev() {
                    if *k == idx {
                        return EvalResult::Ok(v.clone());
                    }
                }
                EvalResult::Ok(*default)
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("Select: expected array".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Evaluate array `store`. Produces a new array value with `(index,
    /// value)` appended as the newest exception on top of the evaluated
    /// base array — `select` resolves ties by walking the exception list
    /// from the end, so this correctly shadows any prior binding for the
    /// same index without needing to search-and-replace here.
    fn eval_store(
        &mut self,
        array: TermId,
        index: TermId,
        value: TermId,
        manager: &TermManager,
    ) -> EvalResult {
        match (
            self.eval(array, manager),
            self.eval(index, manager),
            self.eval(value, manager),
        ) {
            (
                EvalResult::Ok(Value::Array(default, mut excs)),
                EvalResult::Ok(idx),
                EvalResult::Ok(val),
            ) => {
                excs.push((idx, val));
                EvalResult::Ok(Value::Array(default, excs))
            }
            (EvalResult::Ok(_), EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("Store: expected array".to_string())
            }
            (e @ EvalResult::Undefined(_), _, _)
            | (_, e @ EvalResult::Undefined(_), _)
            | (_, _, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _, _)
            | (_, e @ EvalResult::Error(_), _)
            | (_, _, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Evaluate `str.len`. SMT-LIB counts Unicode codepoints, not UTF-8
    /// bytes.
    fn eval_strlen(&mut self, arg: TermId, manager: &TermManager) -> EvalResult {
        match self.eval(arg, manager) {
            EvalResult::Ok(Value::String(s)) => {
                EvalResult::Ok(Value::Int(s.chars().count() as i64))
            }
            EvalResult::Ok(_) => EvalResult::Error("StrLen: expected string".to_string()),
            e => e,
        }
    }

    /// Evaluate `str.++`.
    fn eval_strconcat(&mut self, a: TermId, b: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(a, manager), self.eval(b, manager)) {
            (EvalResult::Ok(Value::String(s1)), EvalResult::Ok(Value::String(s2))) => {
                EvalResult::Ok(Value::String(s1 + s2.as_str()))
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("StrConcat: expected strings".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Evaluate `str.at`: the single-codepoint substring at codepoint
    /// offset `i`, or `""` if `i` is out of `[0, |s|)`.
    fn eval_strat(&mut self, s: TermId, i: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(s, manager), self.eval(i, manager)) {
            (EvalResult::Ok(Value::String(s)), EvalResult::Ok(Value::Int(idx))) => {
                if idx < 0 {
                    EvalResult::Ok(Value::String(String::new()))
                } else {
                    match s.chars().nth(idx as usize) {
                        Some(c) => EvalResult::Ok(Value::String(c.to_string())),
                        None => EvalResult::Ok(Value::String(String::new())),
                    }
                }
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("StrAt: expected (string, int)".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Evaluate `str.contains`.
    fn eval_strcontains(&mut self, s: TermId, sub: TermId, manager: &TermManager) -> EvalResult {
        match (self.eval(s, manager), self.eval(sub, manager)) {
            (EvalResult::Ok(Value::String(h)), EvalResult::Ok(Value::String(n))) => {
                EvalResult::Ok(Value::Bool(h.contains(&n)))
            }
            (EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("StrContains: expected strings".to_string())
            }
            (e @ EvalResult::Undefined(_), _) | (_, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _) | (_, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Evaluate `str.substr` (codepoint offsets; out-of-range/negative
    /// arguments yield `""` per SMT-LIB's total semantics).
    fn eval_strsubstr(
        &mut self,
        s: TermId,
        start: TermId,
        len: TermId,
        manager: &TermManager,
    ) -> EvalResult {
        match (
            self.eval(s, manager),
            self.eval(start, manager),
            self.eval(len, manager),
        ) {
            (
                EvalResult::Ok(Value::String(s)),
                EvalResult::Ok(Value::Int(st)),
                EvalResult::Ok(Value::Int(ln)),
            ) => {
                let char_count = s.chars().count();
                if st < 0 || ln < 0 || st as usize > char_count {
                    return EvalResult::Ok(Value::String(String::new()));
                }
                let start_idx = st as usize;
                let end_idx = start_idx.saturating_add(ln as usize).min(char_count);
                let result: String = s
                    .chars()
                    .skip(start_idx)
                    .take(end_idx - start_idx)
                    .collect();
                EvalResult::Ok(Value::String(result))
            }
            (EvalResult::Ok(_), EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("StrSubstr: expected (string, int, int)".to_string())
            }
            (e @ EvalResult::Undefined(_), _, _)
            | (_, e @ EvalResult::Undefined(_), _)
            | (_, _, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _, _)
            | (_, e @ EvalResult::Error(_), _)
            | (_, _, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Evaluate `str.indexof` (codepoint offsets). Mirrors the SMT-LIB
    /// side condition for an empty needle (`indexof(s, "", i) = i` iff
    /// `0 <= i <= |s|`, else `-1`) and converts the Rust byte-offset match
    /// position back to a codepoint offset for a non-empty needle.
    fn eval_strindexof(
        &mut self,
        haystack: TermId,
        needle: TermId,
        start: TermId,
        manager: &TermManager,
    ) -> EvalResult {
        match (
            self.eval(haystack, manager),
            self.eval(needle, manager),
            self.eval(start, manager),
        ) {
            (
                EvalResult::Ok(Value::String(h)),
                EvalResult::Ok(Value::String(n)),
                EvalResult::Ok(Value::Int(st)),
            ) => {
                if st < 0 {
                    return EvalResult::Ok(Value::Int(-1));
                }
                let start_idx = st as usize;
                let h_char_count = h.chars().count();
                if n.is_empty() {
                    return EvalResult::Ok(Value::Int(if start_idx <= h_char_count {
                        st
                    } else {
                        -1
                    }));
                }
                if start_idx > h_char_count {
                    return EvalResult::Ok(Value::Int(-1));
                }
                let byte_start = h
                    .char_indices()
                    .nth(start_idx)
                    .map(|(b, _)| b)
                    .unwrap_or(h.len());
                match h[byte_start..].find(&n) {
                    Some(byte_pos) => {
                        let char_pos = h[..byte_start + byte_pos].chars().count();
                        EvalResult::Ok(Value::Int(char_pos as i64))
                    }
                    None => EvalResult::Ok(Value::Int(-1)),
                }
            }
            (EvalResult::Ok(_), EvalResult::Ok(_), EvalResult::Ok(_)) => {
                EvalResult::Error("StrIndexOf: expected (string, string, int)".to_string())
            }
            (e @ EvalResult::Undefined(_), _, _)
            | (_, e @ EvalResult::Undefined(_), _)
            | (_, _, e @ EvalResult::Undefined(_)) => e,
            (e @ EvalResult::Error(_), _, _)
            | (_, e @ EvalResult::Error(_), _)
            | (_, _, e @ EvalResult::Error(_)) => e,
        }
    }

    /// Clear the evaluation cache
    pub fn clear_cache(&mut self) {
        self.cache.clear();
    }

    /// Get cache statistics
    pub fn cache_size(&self) -> usize {
        self.cache.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eval_cache() {
        let mut cache = EvalCache::new();
        let t1 = TermId::from(1u32);

        assert!(cache.is_empty());

        cache.insert(t1, Value::Bool(true));
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.get(t1), Some(&Value::Bool(true)));

        cache.clear();
        assert!(cache.is_empty());
    }

    #[test]
    fn test_eval_result() {
        let ok = EvalResult::Ok(Value::Int(42));
        assert!(ok.is_ok());
        assert_eq!(ok.value(), Some(&Value::Int(42)));

        let undef = EvalResult::Undefined(TermId::from(1u32));
        assert!(!undef.is_ok());
        assert_eq!(undef.value(), None);
    }

    // Regression tests for: "Model evaluator silently truncates big integer
    // and wide BV constants to 0" — a BigInt IntConst or BitVecConst that
    // does not fit the fixed-width `Value` representation must surface an
    // explicit `EvalResult::Error`, never a fabricated 0.

    #[test]
    fn test_eval_int_const_in_range_still_works() {
        let mut manager = TermManager::new();
        let model = Model::new();
        let mut evaluator = ModelEvaluator::new(&model);

        let t = manager.mk_int(num_bigint::BigInt::from(42));
        let result = evaluator.eval(t, &manager);
        assert!(matches!(result, EvalResult::Ok(Value::Int(42))));
    }

    #[test]
    fn test_eval_int_const_too_big_for_i64_errors_not_zero() {
        let mut manager = TermManager::new();
        let model = Model::new();
        let mut evaluator = ModelEvaluator::new(&model);

        // 2^100 does not fit in i64; previously this silently evaluated to 0.
        let huge = num_bigint::BigInt::from(2u64).pow(100);
        let t = manager.mk_int(huge);
        let result = evaluator.eval(t, &manager);
        match result {
            EvalResult::Error(_) => {}
            other => panic!("expected EvalResult::Error for oversized IntConst, got {other:?}"),
        }
    }

    #[test]
    fn test_eval_int_const_negative_too_big_errors_not_zero() {
        let mut manager = TermManager::new();
        let model = Model::new();
        let mut evaluator = ModelEvaluator::new(&model);

        let huge_neg = -num_bigint::BigInt::from(2u64).pow(100);
        let t = manager.mk_int(huge_neg);
        let result = evaluator.eval(t, &manager);
        match result {
            EvalResult::Error(_) => {}
            other => {
                panic!("expected EvalResult::Error for oversized negative IntConst, got {other:?}")
            }
        }
    }

    #[test]
    fn test_eval_bitvec_const_in_range_still_works() {
        let mut manager = TermManager::new();
        let model = Model::new();
        let mut evaluator = ModelEvaluator::new(&model);

        let t = manager.mk_bitvec(num_bigint::BigInt::from(7), 8);
        let result = evaluator.eval(t, &manager);
        assert!(matches!(result, EvalResult::Ok(Value::BitVec(8, 7))));
    }

    #[test]
    fn test_eval_wide_bitvec_const_errors_not_zero() {
        let mut manager = TermManager::new();
        let model = Model::new();
        let mut evaluator = ModelEvaluator::new(&model);

        // 128-bit constant with a value that doesn't fit u64; previously
        // this silently evaluated to 0 via `unwrap_or(0)`.
        let wide_val = num_bigint::BigInt::from(2u64).pow(100);
        let t = manager.mk_bitvec(wide_val, 128);
        let result = evaluator.eval(t, &manager);
        match result {
            EvalResult::Error(_) => {}
            other => panic!("expected EvalResult::Error for wide BitVecConst, got {other:?}"),
        }
    }

    #[test]
    fn test_eval_bitvec_const_width_over_64_with_small_value_still_works() {
        let mut manager = TermManager::new();
        let model = Model::new();
        let mut evaluator = ModelEvaluator::new(&model);

        // Width > 64 with a magnitude that fits u64 is exactly representable
        // (Value::BitVec's Display zero-extends the u64 magnitude out to
        // `width` bits), so this must evaluate successfully, not error.
        let t = manager.mk_bitvec(num_bigint::BigInt::from(3), 128);
        let result = evaluator.eval(t, &manager);
        assert!(matches!(result, EvalResult::Ok(Value::BitVec(128, 3))));
    }

    #[test]
    fn test_eval_mod_min_by_neg_one_errors_not_panic() {
        let mut manager = TermManager::new();
        let model = Model::new();
        let mut evaluator = ModelEvaluator::new(&model);

        // `(mod i64::MIN -1)` triggers `i64::MIN.rem_euclid(-1)`, which
        // overflows and panics in BOTH debug and release. It must surface an
        // explicit error rather than aborting the process.
        let min = manager.mk_int(num_bigint::BigInt::from(i64::MIN));
        let neg_one = manager.mk_int(num_bigint::BigInt::from(-1));
        let m = manager.mk_mod(min, neg_one);
        let result = evaluator.eval(m, &manager);
        match result {
            EvalResult::Error(_) => {}
            other => panic!("expected EvalResult::Error for (mod i64::MIN -1), got {other:?}"),
        }
    }

    #[test]
    fn test_eval_mod_euclidean_still_works() {
        let mut manager = TermManager::new();
        let model = Model::new();
        let mut evaluator = ModelEvaluator::new(&model);

        // (mod -7 2) = 1 under Euclidean semantics.
        let a = manager.mk_int(num_bigint::BigInt::from(-7));
        let b = manager.mk_int(num_bigint::BigInt::from(2));
        let m = manager.mk_mod(a, b);
        assert!(matches!(
            evaluator.eval(m, &manager),
            EvalResult::Ok(Value::Int(1))
        ));
    }

    // Regression tests for: "ModelEvaluator cannot evaluate BV
    // comparisons/shifts/div, strings, arrays" — truth tables for the
    // newly implemented BV division/remainder/shift/comparison/
    // concat/extract, array select/store, and string ops.

    fn bv(manager: &mut TermManager, value: i64, width: u32) -> TermId {
        manager.mk_bitvec(num_bigint::BigInt::from(value), width)
    }

    #[test]
    fn test_eval_bvudiv_and_bvurem_truth_table() {
        let mut manager = TermManager::new();
        let model = Model::new();
        let mut evaluator = ModelEvaluator::new(&model);

        let a = bv(&mut manager, 7, 4);
        let b = bv(&mut manager, 2, 4);
        let udiv = manager.mk_bv_udiv(a, b);
        let urem = manager.mk_bv_urem(a, b);
        assert!(matches!(
            evaluator.eval(udiv, &manager),
            EvalResult::Ok(Value::BitVec(4, 3))
        ));
        assert!(matches!(
            evaluator.eval(urem, &manager),
            EvalResult::Ok(Value::BitVec(4, 1))
        ));
    }

    #[test]
    fn test_eval_bvudiv_by_zero_is_all_ones() {
        // SMT-LIB total semantics: (bvudiv x #b0000) = #b1111.
        let mut manager = TermManager::new();
        let model = Model::new();
        let mut evaluator = ModelEvaluator::new(&model);

        let a = bv(&mut manager, 5, 4);
        let zero = bv(&mut manager, 0, 4);
        let udiv = manager.mk_bv_udiv(a, zero);
        assert!(matches!(
            evaluator.eval(udiv, &manager),
            EvalResult::Ok(Value::BitVec(4, 15))
        ));
    }

    #[test]
    fn test_eval_bvurem_by_zero_is_dividend() {
        // SMT-LIB total semantics: (bvurem x #b0000) = x.
        let mut manager = TermManager::new();
        let model = Model::new();
        let mut evaluator = ModelEvaluator::new(&model);

        let a = bv(&mut manager, 5, 4);
        let zero = bv(&mut manager, 0, 4);
        let urem = manager.mk_bv_urem(a, zero);
        assert!(matches!(
            evaluator.eval(urem, &manager),
            EvalResult::Ok(Value::BitVec(4, 5))
        ));
    }

    #[test]
    fn test_eval_bvsdiv_and_bvsrem_truth_table() {
        // -4 (0b1100) / 2 (0b0010) = -2 (0b1110) in 4-bit two's complement.
        let mut manager = TermManager::new();
        let model = Model::new();
        let mut evaluator = ModelEvaluator::new(&model);

        let a = bv(&mut manager, 12, 4); // -4
        let b = bv(&mut manager, 2, 4);
        let sdiv = manager.mk_bv_sdiv(a, b);
        assert!(matches!(
            evaluator.eval(sdiv, &manager),
            EvalResult::Ok(Value::BitVec(4, 14)) // -2
        ));

        // -7 (0b1001) srem 2 (0b0010) = -1 (0b1111): truncating division
        // rounds -7/2 toward zero to -3, remainder -7 - 2*(-3) = -1.
        let c = bv(&mut manager, 9, 4); // -7
        let srem = manager.mk_bv_srem(c, b);
        assert!(matches!(
            evaluator.eval(srem, &manager),
            EvalResult::Ok(Value::BitVec(4, 15)) // -1
        ));
    }

    #[test]
    fn test_eval_bvsdiv_by_zero_depends_on_dividend_sign() {
        // SMT-LIB: (bvsdiv s #b0) = all-ones if s is non-negative, else 1.
        let mut manager = TermManager::new();
        let model = Model::new();
        let mut evaluator = ModelEvaluator::new(&model);

        let zero = bv(&mut manager, 0, 4);
        let pos = bv(&mut manager, 4, 4); // non-negative
        let neg = bv(&mut manager, 12, 4); // -4, negative

        let sdiv_pos = manager.mk_bv_sdiv(pos, zero);
        assert!(matches!(
            evaluator.eval(sdiv_pos, &manager),
            EvalResult::Ok(Value::BitVec(4, 15))
        ));

        let sdiv_neg = manager.mk_bv_sdiv(neg, zero);
        assert!(matches!(
            evaluator.eval(sdiv_neg, &manager),
            EvalResult::Ok(Value::BitVec(4, 1))
        ));
    }

    #[test]
    fn test_eval_bvsrem_by_zero_is_dividend() {
        let mut manager = TermManager::new();
        let model = Model::new();
        let mut evaluator = ModelEvaluator::new(&model);

        let a = bv(&mut manager, 12, 4); // -4
        let zero = bv(&mut manager, 0, 4);
        let srem = manager.mk_bv_srem(a, zero);
        assert!(matches!(
            evaluator.eval(srem, &manager),
            EvalResult::Ok(Value::BitVec(4, 12))
        ));
    }

    #[test]
    fn test_eval_bv_shifts_truth_table() {
        let mut manager = TermManager::new();
        let model = Model::new();
        let mut evaluator = ModelEvaluator::new(&model);

        // shl(0b0011, 1) = 0b0110
        let three = bv(&mut manager, 3, 4);
        let one = bv(&mut manager, 1, 4);
        let shl = manager.mk_bv_shl(three, one);
        assert!(matches!(
            evaluator.eval(shl, &manager),
            EvalResult::Ok(Value::BitVec(4, 6))
        ));

        // shl by an amount >= width zeroes the result.
        let five = bv(&mut manager, 5, 4);
        let shl_oob = manager.mk_bv_shl(three, five);
        assert!(matches!(
            evaluator.eval(shl_oob, &manager),
            EvalResult::Ok(Value::BitVec(4, 0))
        ));

        // lshr(0b1000, 1) = 0b0100 (zero-filled).
        let eight = bv(&mut manager, 8, 4);
        let lshr = manager.mk_bv_lshr(eight, one);
        assert!(matches!(
            evaluator.eval(lshr, &manager),
            EvalResult::Ok(Value::BitVec(4, 4))
        ));

        // ashr(0b1000, 1) = 0b1100 (sign-filled: 0b1000 is -8, -8>>1 = -4).
        let ashr = manager.mk_bv_ashr(eight, one);
        assert!(matches!(
            evaluator.eval(ashr, &manager),
            EvalResult::Ok(Value::BitVec(4, 12))
        ));

        // ashr by an amount >= width on a negative value fills with all
        // ones (saturates toward -1).
        let ashr_oob = manager.mk_bv_ashr(eight, five);
        assert!(matches!(
            evaluator.eval(ashr_oob, &manager),
            EvalResult::Ok(Value::BitVec(4, 15))
        ));
    }

    #[test]
    fn test_eval_bv_comparisons_signed_vs_unsigned() {
        let mut manager = TermManager::new();
        let model = Model::new();
        let mut evaluator = ModelEvaluator::new(&model);

        // 0b1000 = 8 unsigned, -8 signed; 0b0001 = 1 both ways.
        let eight = bv(&mut manager, 8, 4);
        let one = bv(&mut manager, 1, 4);

        let ult = manager.mk_bv_ult(one, eight);
        assert!(matches!(
            evaluator.eval(ult, &manager),
            EvalResult::Ok(Value::Bool(true))
        ));

        let slt = manager.mk_bv_slt(eight, one);
        assert!(
            matches!(
                evaluator.eval(slt, &manager),
                EvalResult::Ok(Value::Bool(true))
            ),
            "signed: -8 < 1"
        );

        let slt_reversed = manager.mk_bv_slt(one, eight);
        assert!(
            matches!(
                evaluator.eval(slt_reversed, &manager),
                EvalResult::Ok(Value::Bool(false))
            ),
            "signed: 1 < -8 is false"
        );

        let sle_eq = manager.mk_bv_sle(eight, eight);
        assert!(matches!(
            evaluator.eval(sle_eq, &manager),
            EvalResult::Ok(Value::Bool(true))
        ));
    }

    #[test]
    fn test_eval_bvconcat_computes_combined_value_and_width() {
        let mut manager = TermManager::new();
        let model = Model::new();
        let mut evaluator = ModelEvaluator::new(&model);

        let lhs = bv(&mut manager, 0b10, 2);
        let rhs = bv(&mut manager, 0b01, 2);
        let concat = manager.mk_bv_concat(lhs, rhs);
        assert!(matches!(
            evaluator.eval(concat, &manager),
            EvalResult::Ok(Value::BitVec(4, 0b1001))
        ));
    }

    #[test]
    fn test_eval_bvconcat_result_wider_than_64_bits_errors() {
        let mut manager = TermManager::new();
        let model = Model::new();
        let mut evaluator = ModelEvaluator::new(&model);

        let lhs = bv(&mut manager, 1, 40);
        let rhs = bv(&mut manager, 1, 30);
        let concat = manager.mk_bv_concat(lhs, rhs);
        match evaluator.eval(concat, &manager) {
            EvalResult::Error(_) => {}
            other => panic!("expected EvalResult::Error for a >64-bit concat, got {other:?}"),
        }
    }

    #[test]
    fn test_eval_bvextract_selects_the_expected_bit_range() {
        let mut manager = TermManager::new();
        let model = Model::new();
        let mut evaluator = ModelEvaluator::new(&model);

        // 181 = 0b10110101; extract [5:2] = 0b1101 = 13.
        let arg = bv(&mut manager, 181, 8);
        let extract = manager.mk_bv_extract(5, 2, arg);
        assert!(matches!(
            evaluator.eval(extract, &manager),
            EvalResult::Ok(Value::BitVec(4, 13))
        ));
    }

    #[test]
    fn test_eval_select_and_store_array_roundtrip() {
        let mut manager = TermManager::new();
        let mut model = Model::new();

        let int_sort = manager.sorts.int_sort;
        let array_sort = manager.sorts.array(int_sort, int_sort);
        let arr = manager.mk_var("arr", array_sort);
        model.assign(arr, Value::Array(Box::new(Value::Int(0)), Vec::new()));

        let five = manager.mk_int(num_bigint::BigInt::from(5));
        let forty_two = manager.mk_int(num_bigint::BigInt::from(42));
        let stored = manager.mk_store(arr, five, forty_two);

        let mut evaluator = ModelEvaluator::new(&model);

        let select_stored = manager.mk_select(stored, five);
        assert!(matches!(
            evaluator.eval(select_stored, &manager),
            EvalResult::Ok(Value::Int(42))
        ));

        // An index never stored falls back to the array's default value.
        let six = manager.mk_int(num_bigint::BigInt::from(6));
        let select_default = manager.mk_select(stored, six);
        assert!(matches!(
            evaluator.eval(select_default, &manager),
            EvalResult::Ok(Value::Int(0))
        ));

        // A second store to the same index shadows the first.
        let hundred = manager.mk_int(num_bigint::BigInt::from(100));
        let stored_again = manager.mk_store(stored, five, hundred);
        let select_latest = manager.mk_select(stored_again, five);
        assert!(matches!(
            evaluator.eval(select_latest, &manager),
            EvalResult::Ok(Value::Int(100))
        ));
    }

    #[test]
    fn test_eval_string_ops_truth_table() {
        let mut manager = TermManager::new();
        let model = Model::new();
        let mut evaluator = ModelEvaluator::new(&model);

        let hello = manager.mk_string_lit("hello");
        let world = manager.mk_string_lit(" world");

        let len = manager.mk_str_len(hello);
        assert!(matches!(
            evaluator.eval(len, &manager),
            EvalResult::Ok(Value::Int(5))
        ));

        let concat = manager.mk_str_concat(hello, world);
        match evaluator.eval(concat, &manager) {
            EvalResult::Ok(Value::String(s)) => assert_eq!(s, "hello world"),
            other => panic!("expected concatenated string, got {other:?}"),
        }

        let one = manager.mk_int(num_bigint::BigInt::from(1));
        let at = manager.mk_str_at(hello, one);
        match evaluator.eval(at, &manager) {
            EvalResult::Ok(Value::String(s)) => assert_eq!(s, "e"),
            other => panic!("expected \"e\", got {other:?}"),
        }

        let ell = manager.mk_string_lit("ell");
        let contains_true = manager.mk_str_contains(hello, ell);
        assert!(matches!(
            evaluator.eval(contains_true, &manager),
            EvalResult::Ok(Value::Bool(true))
        ));

        let xyz = manager.mk_string_lit("xyz");
        let contains_false = manager.mk_str_contains(hello, xyz);
        assert!(matches!(
            evaluator.eval(contains_false, &manager),
            EvalResult::Ok(Value::Bool(false))
        ));

        let three = manager.mk_int(num_bigint::BigInt::from(3));
        let substr = manager.mk_str_substr(hello, one, three);
        match evaluator.eval(substr, &manager) {
            EvalResult::Ok(Value::String(s)) => assert_eq!(s, "ell"),
            other => panic!("expected \"ell\", got {other:?}"),
        }

        let zero = manager.mk_int(num_bigint::BigInt::from(0));
        let l = manager.mk_string_lit("l");
        let indexof = manager.mk_str_indexof(hello, l, zero);
        assert!(matches!(
            evaluator.eval(indexof, &manager),
            EvalResult::Ok(Value::Int(2))
        ));

        // Not found -> -1.
        let indexof_missing = manager.mk_str_indexof(hello, xyz, zero);
        assert!(matches!(
            evaluator.eval(indexof_missing, &manager),
            EvalResult::Ok(Value::Int(-1))
        ));
    }
}
