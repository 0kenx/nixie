//! Model Evaluator
//!
//! Evaluates terms under a given model assignment.

use super::{Model, Value};
use crate::ast::{TermId, TermKind, TermManager};
use crate::prelude::HashMap;
#[allow(unused_imports)]
use crate::prelude::*;
use num_rational::Rational64;

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
}
