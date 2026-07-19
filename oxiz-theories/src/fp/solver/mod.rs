// Copyright 2026 COOLJAPAN OU (Team KitaSan)
// SPDX-License-Identifier: Apache-2.0

#[allow(unused_imports)]
use crate::prelude::*;
use crate::theory::{EqualityNotification, Theory, TheoryCombination, TheoryId, TheoryResult};
use oxiz_core::ast::TermId;
use oxiz_core::error::Result;
use oxiz_sat::{LBool, Lit, Solver as SatSolver, SolverResult, Var};
use smallvec::SmallVec;
/// IEEE 754 Floating-point format specification
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FpFormat {
    /// Number of bits in the exponent
    pub exponent_bits: u32,
    /// Number of bits in the significand (including implicit bit)
    pub significand_bits: u32,
}
impl FpFormat {
    /// IEEE 754 binary16 (half precision)
    pub const FLOAT16: Self = Self {
        exponent_bits: 5,
        significand_bits: 11,
    };
    /// IEEE 754 binary32 (single precision)
    pub const FLOAT32: Self = Self {
        exponent_bits: 8,
        significand_bits: 24,
    };
    /// IEEE 754 binary64 (double precision)
    pub const FLOAT64: Self = Self {
        exponent_bits: 11,
        significand_bits: 53,
    };
    /// IEEE 754 binary128 (quad precision)
    pub const FLOAT128: Self = Self {
        exponent_bits: 15,
        significand_bits: 113,
    };
    /// Create a custom floating-point format
    #[must_use]
    pub const fn new(exponent_bits: u32, significand_bits: u32) -> Self {
        Self {
            exponent_bits,
            significand_bits,
        }
    }
    /// Total width in bits
    #[must_use]
    pub const fn width(&self) -> u32 {
        1 + self.exponent_bits + self.significand_bits - 1
    }
    /// Exponent bias (2^(e-1) - 1)
    #[must_use]
    pub const fn bias(&self) -> i32 {
        (1 << (self.exponent_bits - 1)) - 1
    }
    /// Maximum exponent value (all 1s)
    #[must_use]
    pub const fn max_exponent(&self) -> u32 {
        (1 << self.exponent_bits) - 1
    }
}
/// IEEE 754 Rounding modes
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum FpRoundingMode {
    /// Round to nearest, ties to even (default)
    #[default]
    RoundNearestTiesToEven,
    /// Round to nearest, ties away from zero
    RoundNearestTiesToAway,
    /// Round toward positive infinity
    RoundTowardPositive,
    /// Round toward negative infinity
    RoundTowardNegative,
    /// Round toward zero (truncate)
    RoundTowardZero,
}
impl FpRoundingMode {
    /// SMT-LIB2 name
    #[must_use]
    pub const fn smtlib_name(&self) -> &'static str {
        match self {
            Self::RoundNearestTiesToEven => "RNE",
            Self::RoundNearestTiesToAway => "RNA",
            Self::RoundTowardPositive => "RTP",
            Self::RoundTowardNegative => "RTN",
            Self::RoundTowardZero => "RTZ",
        }
    }
}
/// A floating-point value representation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FpValue {
    /// Sign bit (true = negative)
    pub sign: bool,
    /// Exponent bits (biased)
    pub exponent: u64,
    /// Significand bits (without implicit bit for normal numbers)
    pub significand: u64,
    /// Format specification
    pub format: FpFormat,
}
impl FpValue {
    /// Create positive zero
    #[must_use]
    pub fn pos_zero(format: FpFormat) -> Self {
        Self {
            sign: false,
            exponent: 0,
            significand: 0,
            format,
        }
    }
    /// Create negative zero
    #[must_use]
    pub fn neg_zero(format: FpFormat) -> Self {
        Self {
            sign: true,
            exponent: 0,
            significand: 0,
            format,
        }
    }
    /// Create positive infinity
    #[must_use]
    pub fn pos_infinity(format: FpFormat) -> Self {
        Self {
            sign: false,
            exponent: format.max_exponent() as u64,
            significand: 0,
            format,
        }
    }
    /// Create negative infinity
    #[must_use]
    pub fn neg_infinity(format: FpFormat) -> Self {
        Self {
            sign: true,
            exponent: format.max_exponent() as u64,
            significand: 0,
            format,
        }
    }
    /// Create canonical NaN
    #[must_use]
    pub fn nan(format: FpFormat) -> Self {
        Self {
            sign: false,
            exponent: format.max_exponent() as u64,
            significand: 1 << (format.significand_bits - 2),
            format,
        }
    }
    /// Check if this is zero (positive or negative)
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.exponent == 0 && self.significand == 0
    }
    /// Check if this is subnormal (denormalized)
    #[must_use]
    pub fn is_subnormal(&self) -> bool {
        self.exponent == 0 && self.significand != 0
    }
    /// Check if this is normal
    #[must_use]
    pub fn is_normal(&self) -> bool {
        let max_exp = self.format.max_exponent() as u64;
        self.exponent > 0 && self.exponent < max_exp
    }
    /// Check if this is infinity
    #[must_use]
    pub fn is_infinite(&self) -> bool {
        self.exponent == self.format.max_exponent() as u64 && self.significand == 0
    }
    /// Check if this is NaN
    #[must_use]
    pub fn is_nan(&self) -> bool {
        self.exponent == self.format.max_exponent() as u64 && self.significand != 0
    }
    /// Check if negative
    #[must_use]
    pub fn is_negative(&self) -> bool {
        self.sign && !self.is_nan()
    }
    /// Check if positive
    #[must_use]
    pub fn is_positive(&self) -> bool {
        !self.sign && !self.is_nan()
    }
    /// Convert from f32
    #[must_use]
    pub fn from_f32(val: f32) -> Self {
        let bits = val.to_bits();
        Self {
            sign: (bits >> 31) != 0,
            exponent: ((bits >> 23) & 0xFF) as u64,
            significand: (bits & 0x7FFFFF) as u64,
            format: FpFormat::FLOAT32,
        }
    }
    /// Convert from f64
    #[must_use]
    pub fn from_f64(val: f64) -> Self {
        let bits = val.to_bits();
        Self {
            sign: (bits >> 63) != 0,
            exponent: (bits >> 52) & 0x7FF,
            significand: bits & 0xFFFFFFFFFFFFF,
            format: FpFormat::FLOAT64,
        }
    }
    /// Convert to f32 (only valid for FLOAT32 format)
    #[must_use]
    pub fn to_f32(&self) -> Option<f32> {
        if self.format != FpFormat::FLOAT32 {
            return None;
        }
        let mut bits: u32 = 0;
        if self.sign {
            bits |= 1 << 31;
        }
        bits |= (self.exponent as u32 & 0xFF) << 23;
        bits |= self.significand as u32 & 0x7FFFFF;
        Some(f32::from_bits(bits))
    }
    /// Convert to f64 (only valid for FLOAT64 format)
    #[must_use]
    pub fn to_f64(&self) -> Option<f64> {
        if self.format != FpFormat::FLOAT64 {
            return None;
        }
        let mut bits: u64 = 0;
        if self.sign {
            bits |= 1 << 63;
        }
        bits |= (self.exponent & 0x7FF) << 52;
        bits |= self.significand & 0xFFFFFFFFFFFFF;
        Some(f64::from_bits(bits))
    }
}
/// A floating-point variable (set of SAT variables)
#[derive(Debug, Clone)]
struct FpVar {
    /// Sign bit
    sign: Var,
    /// Exponent bits (LSB first)
    exponent: SmallVec<[Var; 16]>,
    /// Significand bits (LSB first, without implicit bit)
    significand: SmallVec<[Var; 64]>,
    /// Format
    format: FpFormat,
}
/// Floating-Point Theory Solver
#[derive(Debug)]
pub struct FpSolver {
    /// Embedded SAT solver
    sat: SatSolver,
    /// Term to FP variable mapping
    term_to_fp: FxHashMap<TermId, FpVar>,
    /// Pending assertions
    assertions: Vec<(TermId, bool)>,
    /// Context stack. Each entry records `(assertions.len(),
    /// has_unsupported_conversion)` at push time so `pop` restores both.
    context_stack: Vec<(usize, bool)>,
    /// Current rounding mode
    rounding_mode: FpRoundingMode,
    /// Set to `true` when an FP<->integer / FP<->real conversion whose
    /// bit-blasting this solver does not (yet) constrain has been asserted
    /// (see the conversion methods below). While set, a `Sat` verdict from
    /// the embedded SAT solver is NOT trustworthy -- the conversion's result
    /// bits are unconstrained, so `check()` must report `Unknown` rather than
    /// silently claiming `Sat` on a model that ignores the conversion
    /// semantics. `Unsat` remains sound (it holds regardless of the free
    /// conversion bits) and is still reported.
    has_unsupported_conversion: bool,
    /// Shared equalities derived by FP theory for Nelson-Oppen combination.
    /// FP is typically a "polite" theory -- it rarely generates shared equalities,
    /// but may do so from rounding mode constraints or value equivalences.
    shared_equalities: Vec<EqualityNotification>,
    /// Pending equality notifications from other theories
    equality_notifications: Vec<EqualityNotification>,
    /// Snapshot of the satisfying SAT assignment captured at the end of the
    /// last successful `check()`, taken BEFORE the incremental-probe
    /// residue (trail position, learned clauses) is rolled back. `get_model`
    /// must read through this snapshot rather than the live trail: once a
    /// probe's residue is discarded the live trail reverts to the
    /// committed (asserted) prefix, which reads as all-`Undef` for any
    /// variable only assigned during search.
    last_sat_model: Vec<LBool>,
}
impl Default for FpSolver {
    fn default() -> Self {
        Self::new()
    }
}
impl FpSolver {
    /// Create a new Floating-Point solver
    #[must_use]
    pub fn new() -> Self {
        Self {
            sat: SatSolver::new(),
            term_to_fp: FxHashMap::default(),
            assertions: Vec::new(),
            context_stack: Vec::new(),
            rounding_mode: FpRoundingMode::default(),
            has_unsupported_conversion: false,
            shared_equalities: Vec::new(),
            equality_notifications: Vec::new(),
            last_sat_model: Vec::new(),
        }
    }
    /// Set the rounding mode
    pub fn set_rounding_mode(&mut self, mode: FpRoundingMode) {
        self.rounding_mode = mode;
    }
    /// Get the current rounding mode
    #[must_use]
    pub fn rounding_mode(&self) -> FpRoundingMode {
        self.rounding_mode
    }
    /// Create a new floating-point variable
    pub fn new_fp(&mut self, term: TermId, format: FpFormat) {
        if self.term_to_fp.contains_key(&term) {
            return;
        }
        let sign = self.sat.new_var();
        let exponent: SmallVec<[Var; 16]> = (0..format.exponent_bits)
            .map(|_| self.sat.new_var())
            .collect();
        let significand: SmallVec<[Var; 64]> = (0..format.significand_bits - 1)
            .map(|_| self.sat.new_var())
            .collect();
        self.term_to_fp.insert(
            term,
            FpVar {
                sign,
                exponent,
                significand,
                format,
            },
        );
    }
    /// Assert a constant floating-point value
    pub fn assert_const(&mut self, term: TermId, value: &FpValue) {
        self.new_fp(term, value.format);
        let fp = match self.term_to_fp.get(&term).cloned() {
            Some(fp) => fp,
            None => return,
        };
        if value.sign {
            self.sat.add_clause([Lit::pos(fp.sign)]);
        } else {
            self.sat.add_clause([Lit::neg(fp.sign)]);
        }
        for (i, &var) in fp.exponent.iter().enumerate() {
            if (value.exponent >> i) & 1 == 1 {
                self.sat.add_clause([Lit::pos(var)]);
            } else {
                self.sat.add_clause([Lit::neg(var)]);
            }
        }
        for (i, &var) in fp.significand.iter().enumerate() {
            if (value.significand >> i) & 1 == 1 {
                self.sat.add_clause([Lit::pos(var)]);
            } else {
                self.sat.add_clause([Lit::neg(var)]);
            }
        }
    }
    /// Encode `out <=> (a OR b)` allocating a fresh output variable.
    fn new_or(&mut self, a: Var, b: Var) -> Var {
        let out = self.sat.new_var();
        self.encode_or(out, a, b);
        out
    }
    /// Encode raw bitwise equality of two FP encodings: `result <=> (sign_a
    /// = sign_b) AND (exp_a = exp_b) AND (sig_a = sig_b)`. This is a purely
    /// syntactic comparison of the underlying bit-vector encoding and does
    /// not, by itself, implement either SMT-LIB `=` or `fp.eq` semantics.
    fn encode_fp_bitwise_eq(&mut self, va: &FpVar, vb: &FpVar) -> Var {
        let sign_eq = self.sat.new_var();
        self.encode_xnor(sign_eq, va.sign, vb.sign);
        let mut acc = sign_eq;
        for (ea, eb) in va.exponent.iter().zip(vb.exponent.iter()) {
            let bit_eq = self.sat.new_var();
            self.encode_xnor(bit_eq, *ea, *eb);
            acc = self.new_and(acc, bit_eq);
        }
        for (sa, sb) in va.significand.iter().zip(vb.significand.iter()) {
            let bit_eq = self.sat.new_var();
            self.encode_xnor(bit_eq, *sa, *sb);
            acc = self.new_and(acc, bit_eq);
        }
        acc
    }
    /// Assert structural (SMT-LIB `=`) FP equality: `a = b`.
    ///
    /// Per the SMT-LIB FloatingPoint theory, `NaN` is a single abstract
    /// value: any two NaN-valued terms are equal under `=`, regardless of
    /// their concrete sign/significand encoding (quiet vs. signaling,
    /// differing payloads, etc). Non-NaN values compare bitwise, so `+0`
    /// and `-0` -- which have distinct bit patterns -- are correctly
    /// unequal under `=`. This is distinct from `fp.eq`, which additionally
    /// treats `+0` and `-0` as equal and treats NaN as unequal to
    /// everything (including itself); see [`Self::assert_fp_ieee_eq`].
    pub fn assert_fp_eq(&mut self, a: TermId, b: TermId) {
        let fp_a = self.term_to_fp.get(&a).cloned();
        let fp_b = self.term_to_fp.get(&b).cloned();
        if let (Some(va), Some(vb)) = (fp_a, fp_b) {
            assert_eq!(va.format, vb.format);
            let a_is_nan = self.encode_is_nan(&va);
            let b_is_nan = self.encode_is_nan(&vb);
            let both_nan = self.new_and(a_is_nan, b_is_nan);
            let bitwise_eq = self.encode_fp_bitwise_eq(&va, &vb);
            let holds = self.new_or(both_nan, bitwise_eq);
            self.sat.add_clause([Lit::pos(holds)]);
        }
    }
    /// Encode IEEE-754 `fp.eq` semantics: `result <=> fp.eq(a, b)`.
    ///
    /// - Either operand NaN => false (including `fp.eq(NaN, NaN)`).
    /// - `+0` and `-0` compare equal.
    /// - Otherwise, equal iff the bit encodings match exactly.
    fn encode_fp_ieee_eq(&mut self, va: &FpVar, vb: &FpVar) -> Var {
        let is_nan_a = self.encode_is_nan(va);
        let is_nan_b = self.encode_is_nan(vb);
        let is_zero_a = self.encode_is_zero(va);
        let is_zero_b = self.encode_is_zero(vb);
        let bitwise_eq = self.encode_fp_bitwise_eq(va, vb);
        let both_zero = self.new_and(is_zero_a, is_zero_b);
        let eq_or_both_zero = self.new_or(bitwise_eq, both_zero);
        let not_nan_a = self.new_not(is_nan_a);
        let not_nan_b = self.new_not(is_nan_b);
        let step = self.new_and(eq_or_both_zero, not_nan_a);
        self.new_and(step, not_nan_b)
    }
    /// Assert/reify IEEE-754 comparison: `result <=> fp.eq(a, b)`.
    ///
    /// Returns a fully reified SAT variable following SMT-LIB `fp.eq`
    /// semantics (NaN is unequal to everything including itself; `+0` and
    /// `-0` compare equal).
    pub fn assert_fp_ieee_eq(&mut self, a: TermId, b: TermId) -> Var {
        let fp_a = self.term_to_fp.get(&a).cloned();
        let fp_b = self.term_to_fp.get(&b).cloned();
        let result = self.sat.new_var();
        if let (Some(va), Some(vb)) = (fp_a, fp_b) {
            assert_eq!(va.format, vb.format);
            let eq = self.encode_fp_ieee_eq(&va, &vb);
            self.encode_bit_eq(result, eq);
        }
        result
    }
    /// Encode "is NaN" predicate, returns variable that is true iff the value is NaN
    fn encode_is_nan(&mut self, fp: &FpVar) -> Var {
        let is_nan = self.sat.new_var();
        let exp_max = self.sat.new_var();
        for &e in &fp.exponent {
            self.sat.add_clause([Lit::neg(exp_max), Lit::pos(e)]);
        }
        let mut clause: SmallVec<[Lit; 16]> = SmallVec::new();
        clause.push(Lit::pos(exp_max));
        for &e in &fp.exponent {
            clause.push(Lit::neg(e));
        }
        self.sat.add_clause(clause);
        let sig_nonzero = self.sat.new_var();
        for &s in &fp.significand {
            self.sat.add_clause([Lit::neg(s), Lit::pos(sig_nonzero)]);
        }
        let mut clause: SmallVec<[Lit; 64]> = SmallVec::new();
        clause.push(Lit::neg(sig_nonzero));
        for &s in &fp.significand {
            clause.push(Lit::pos(s));
        }
        self.sat.add_clause(clause);
        self.sat.add_clause([Lit::neg(is_nan), Lit::pos(exp_max)]);
        self.sat
            .add_clause([Lit::neg(is_nan), Lit::pos(sig_nonzero)]);
        self.sat
            .add_clause([Lit::neg(exp_max), Lit::neg(sig_nonzero), Lit::pos(is_nan)]);
        is_nan
    }
    /// Encode "is Infinite" predicate
    fn encode_is_infinite(&mut self, fp: &FpVar) -> Var {
        let is_inf = self.sat.new_var();
        let exp_max = self.sat.new_var();
        for &e in &fp.exponent {
            self.sat.add_clause([Lit::neg(exp_max), Lit::pos(e)]);
        }
        let mut clause: SmallVec<[Lit; 16]> = SmallVec::new();
        clause.push(Lit::pos(exp_max));
        for &e in &fp.exponent {
            clause.push(Lit::neg(e));
        }
        self.sat.add_clause(clause);
        let sig_zero = self.sat.new_var();
        for &s in &fp.significand {
            self.sat.add_clause([Lit::neg(sig_zero), Lit::neg(s)]);
        }
        let mut clause: SmallVec<[Lit; 64]> = SmallVec::new();
        clause.push(Lit::pos(sig_zero));
        for &s in &fp.significand {
            clause.push(Lit::pos(s));
        }
        self.sat.add_clause(clause);
        self.sat.add_clause([Lit::neg(is_inf), Lit::pos(exp_max)]);
        self.sat.add_clause([Lit::neg(is_inf), Lit::pos(sig_zero)]);
        self.sat
            .add_clause([Lit::neg(exp_max), Lit::neg(sig_zero), Lit::pos(is_inf)]);
        is_inf
    }
    /// Encode "is Zero" predicate
    fn encode_is_zero(&mut self, fp: &FpVar) -> Var {
        let is_zero = self.sat.new_var();
        let exp_zero = self.sat.new_var();
        for &e in &fp.exponent {
            self.sat.add_clause([Lit::neg(exp_zero), Lit::neg(e)]);
        }
        let mut clause: SmallVec<[Lit; 16]> = SmallVec::new();
        clause.push(Lit::pos(exp_zero));
        for &e in &fp.exponent {
            clause.push(Lit::pos(e));
        }
        self.sat.add_clause(clause);
        let sig_zero = self.sat.new_var();
        for &s in &fp.significand {
            self.sat.add_clause([Lit::neg(sig_zero), Lit::neg(s)]);
        }
        let mut clause: SmallVec<[Lit; 64]> = SmallVec::new();
        clause.push(Lit::pos(sig_zero));
        for &s in &fp.significand {
            clause.push(Lit::pos(s));
        }
        self.sat.add_clause(clause);
        self.sat.add_clause([Lit::neg(is_zero), Lit::pos(exp_zero)]);
        self.sat.add_clause([Lit::neg(is_zero), Lit::pos(sig_zero)]);
        self.sat
            .add_clause([Lit::neg(exp_zero), Lit::neg(sig_zero), Lit::pos(is_zero)]);
        is_zero
    }
    /// Assert that a term is NaN
    pub fn assert_is_nan(&mut self, term: TermId) {
        if let Some(fp) = self.term_to_fp.get(&term).cloned() {
            let is_nan = self.encode_is_nan(&fp);
            self.sat.add_clause([Lit::pos(is_nan)]);
        }
    }
    /// Assert that a term is infinite
    pub fn assert_is_infinite(&mut self, term: TermId) {
        if let Some(fp) = self.term_to_fp.get(&term).cloned() {
            let is_inf = self.encode_is_infinite(&fp);
            self.sat.add_clause([Lit::pos(is_inf)]);
        }
    }
    /// Assert that a term is zero
    pub fn assert_is_zero(&mut self, term: TermId) {
        if let Some(fp) = self.term_to_fp.get(&term).cloned() {
            let is_zero = self.encode_is_zero(&fp);
            self.sat.add_clause([Lit::pos(is_zero)]);
        }
    }
    /// Assert that a term is normal
    pub fn assert_is_normal(&mut self, term: TermId) {
        if let Some(fp) = self.term_to_fp.get(&term).cloned() {
            let is_nan = self.encode_is_nan(&fp);
            let is_inf = self.encode_is_infinite(&fp);
            let is_zero = self.encode_is_zero(&fp);
            let exp_nonzero = self.sat.new_var();
            for &e in &fp.exponent {
                self.sat.add_clause([Lit::neg(e), Lit::pos(exp_nonzero)]);
            }
            let mut clause: SmallVec<[Lit; 16]> = SmallVec::new();
            clause.push(Lit::neg(exp_nonzero));
            for &e in &fp.exponent {
                clause.push(Lit::pos(e));
            }
            self.sat.add_clause(clause);
            self.sat.add_clause([Lit::pos(exp_nonzero)]);
            self.sat.add_clause([Lit::neg(is_nan)]);
            self.sat.add_clause([Lit::neg(is_inf)]);
            self.sat.add_clause([Lit::neg(is_zero)]);
        }
    }
    /// Assert negation: result = -operand
    pub fn assert_fp_neg(&mut self, result: TermId, operand: TermId) {
        let fp_op = self.term_to_fp.get(&operand).cloned();
        let fp_res = self.term_to_fp.get(&result).cloned();
        if let (Some(op), Some(res)) = (fp_op, fp_res) {
            assert_eq!(op.format, res.format);
            self.sat.add_clause([Lit::neg(res.sign), Lit::neg(op.sign)]);
            self.sat.add_clause([Lit::pos(res.sign), Lit::pos(op.sign)]);
            for (re, oe) in res.exponent.iter().zip(op.exponent.iter()) {
                self.sat.add_clause([Lit::neg(*re), Lit::pos(*oe)]);
                self.sat.add_clause([Lit::pos(*re), Lit::neg(*oe)]);
            }
            for (rs, os) in res.significand.iter().zip(op.significand.iter()) {
                self.sat.add_clause([Lit::neg(*rs), Lit::pos(*os)]);
                self.sat.add_clause([Lit::pos(*rs), Lit::neg(*os)]);
            }
        }
    }
    /// Assert absolute value: result = |operand|
    pub fn assert_fp_abs(&mut self, result: TermId, operand: TermId) {
        let fp_op = self.term_to_fp.get(&operand).cloned();
        let fp_res = self.term_to_fp.get(&result).cloned();
        if let (Some(op), Some(res)) = (fp_op, fp_res) {
            assert_eq!(op.format, res.format);
            self.sat.add_clause([Lit::neg(res.sign)]);
            for (re, oe) in res.exponent.iter().zip(op.exponent.iter()) {
                self.sat.add_clause([Lit::neg(*re), Lit::pos(*oe)]);
                self.sat.add_clause([Lit::pos(*re), Lit::neg(*oe)]);
            }
            for (rs, os) in res.significand.iter().zip(op.significand.iter()) {
                self.sat.add_clause([Lit::neg(*rs), Lit::pos(*os)]);
                self.sat.add_clause([Lit::pos(*rs), Lit::neg(*os)]);
            }
        }
    }
    /// Encode a full biconditional AND gate: `out <=> (a AND b)`.
    fn encode_and(&mut self, out: Var, a: Var, b: Var) {
        self.sat.add_clause([Lit::neg(out), Lit::pos(a)]);
        self.sat.add_clause([Lit::neg(out), Lit::pos(b)]);
        self.sat
            .add_clause([Lit::pos(out), Lit::neg(a), Lit::neg(b)]);
    }
    /// Encode a full biconditional OR gate: `out <=> (a OR b)`.
    fn encode_or(&mut self, out: Var, a: Var, b: Var) {
        self.sat
            .add_clause([Lit::neg(out), Lit::pos(a), Lit::pos(b)]);
        self.sat.add_clause([Lit::pos(out), Lit::neg(a)]);
        self.sat.add_clause([Lit::pos(out), Lit::neg(b)]);
    }
    /// Encode a full biconditional XOR gate: `out <=> (a XOR b)`.
    fn encode_xor(&mut self, out: Var, a: Var, b: Var) {
        self.sat
            .add_clause([Lit::neg(out), Lit::neg(a), Lit::neg(b)]);
        self.sat
            .add_clause([Lit::neg(out), Lit::pos(a), Lit::pos(b)]);
        self.sat
            .add_clause([Lit::pos(out), Lit::neg(a), Lit::pos(b)]);
        self.sat
            .add_clause([Lit::pos(out), Lit::pos(a), Lit::neg(b)]);
    }
    /// Encode a full biconditional XNOR gate: `out <=> (a <=> b)`.
    fn encode_xnor(&mut self, out: Var, a: Var, b: Var) {
        self.sat
            .add_clause([Lit::neg(out), Lit::neg(a), Lit::pos(b)]);
        self.sat
            .add_clause([Lit::neg(out), Lit::pos(a), Lit::neg(b)]);
        self.sat
            .add_clause([Lit::pos(out), Lit::pos(a), Lit::pos(b)]);
        self.sat
            .add_clause([Lit::pos(out), Lit::neg(a), Lit::neg(b)]);
    }
    /// Encode `out <=> ~a`.
    fn encode_not(&mut self, out: Var, a: Var) {
        self.sat.add_clause([Lit::pos(out), Lit::pos(a)]);
        self.sat.add_clause([Lit::neg(out), Lit::neg(a)]);
    }
    /// Encode `out <=> (~a AND b)`.
    fn encode_and_not_a(&mut self, out: Var, a: Var, b: Var) {
        self.sat.add_clause([Lit::neg(out), Lit::neg(a)]);
        self.sat.add_clause([Lit::neg(out), Lit::pos(b)]);
        self.sat
            .add_clause([Lit::pos(out), Lit::pos(a), Lit::neg(b)]);
    }
    /// Encode a full biconditional multiplexer: `out <=> (sel ? if_true : if_false)`.
    fn encode_mux(&mut self, out: Var, sel: Var, if_true: Var, if_false: Var) {
        self.sat
            .add_clause([Lit::neg(sel), Lit::neg(if_true), Lit::pos(out)]);
        self.sat
            .add_clause([Lit::neg(sel), Lit::pos(if_true), Lit::neg(out)]);
        self.sat
            .add_clause([Lit::pos(sel), Lit::neg(if_false), Lit::pos(out)]);
        self.sat
            .add_clause([Lit::pos(sel), Lit::pos(if_false), Lit::neg(out)]);
    }
    /// Force two SAT variables to be logically equivalent: `a <=> b`.
    fn encode_bit_eq(&mut self, a: Var, b: Var) {
        self.sat.add_clause([Lit::neg(a), Lit::pos(b)]);
        self.sat.add_clause([Lit::pos(a), Lit::neg(b)]);
    }
    /// Allocate a fresh SAT variable bound to `a AND b`.
    fn new_and(&mut self, a: Var, b: Var) -> Var {
        let out = self.sat.new_var();
        self.encode_and(out, a, b);
        out
    }
    /// Allocate a fresh SAT variable bound to `~a`.
    fn new_not(&mut self, a: Var) -> Var {
        let out = self.sat.new_var();
        self.encode_not(out, a);
        out
    }
    /// Allocate a fresh SAT variable bound to `a XOR b`.
    fn new_xor(&mut self, a: Var, b: Var) -> Var {
        let out = self.sat.new_var();
        self.encode_xor(out, a, b);
        out
    }
    /// Allocate a fresh SAT variable bound to `sel ? if_true : if_false`.
    fn new_mux(&mut self, sel: Var, if_true: Var, if_false: Var) -> Var {
        let out = self.sat.new_var();
        self.encode_mux(out, sel, if_true, if_false);
        out
    }
    /// Encode an unsigned less-than comparator over equal-length bit vectors
    /// (LSB-first: index 0 is the least significant bit), returning a fully
    /// reified variable: `result <=> (a < b)` as unsigned integers.
    fn encode_ult(&mut self, a_bits: &[Var], b_bits: &[Var]) -> Var {
        debug_assert_eq!(a_bits.len(), b_bits.len());
        let width = a_bits.len();
        if width == 0 {
            let result = self.sat.new_var();
            self.sat.add_clause([Lit::neg(result)]);
            return result;
        }
        let mut lt_prev = self.sat.new_var();
        self.encode_and_not_a(lt_prev, a_bits[0], b_bits[0]);
        for i in 1..width {
            let ai = a_bits[i];
            let bi = b_bits[i];
            let lt_at_i = self.sat.new_var();
            self.encode_and_not_a(lt_at_i, ai, bi);
            let eq_i = self.sat.new_var();
            self.encode_xnor(eq_i, ai, bi);
            let carry_prev = self.sat.new_var();
            self.encode_and(carry_prev, eq_i, lt_prev);
            let lt_next = self.sat.new_var();
            self.encode_or(lt_next, lt_at_i, carry_prev);
            lt_prev = lt_next;
        }
        lt_prev
    }
    /// Encode IEEE-754 total-order strict less-than: `result <=> (a < b)`,
    /// per SMT-LIB `fp.lt` semantics (see Z3's `fpa2bv_converter.cpp`):
    /// - Either operand NaN => false.
    /// - +0 and -0 compare equal (neither is less than the other).
    /// - Different signs: the negative operand is smaller, unless both are
    ///   zero (already handled above).
    /// - Same sign: compare (exponent, significand) as an unsigned magnitude,
    ///   reversing the order for negative operands (larger magnitude =>
    ///   smaller value).
    fn encode_fp_lt(&mut self, va: &FpVar, vb: &FpVar) -> Var {
        let is_nan_a = self.encode_is_nan(va);
        let is_nan_b = self.encode_is_nan(vb);
        let is_zero_a = self.encode_is_zero(va);
        let is_zero_b = self.encode_is_zero(vb);
        let mut mag_a: SmallVec<[Var; 128]> = SmallVec::new();
        mag_a.extend(va.significand.iter().copied());
        mag_a.extend(va.exponent.iter().copied());
        let mut mag_b: SmallVec<[Var; 128]> = SmallVec::new();
        mag_b.extend(vb.significand.iter().copied());
        mag_b.extend(vb.exponent.iter().copied());
        let mag_lt_ab = self.encode_ult(&mag_a, &mag_b);
        let mag_lt_ba = self.encode_ult(&mag_b, &mag_a);
        let diff_sign = self.new_xor(va.sign, vb.sign);
        let same_sign_result = self.new_mux(va.sign, mag_lt_ba, mag_lt_ab);
        let raw = self.new_mux(diff_sign, va.sign, same_sign_result);
        let both_zero = self.new_and(is_zero_a, is_zero_b);
        let not_both_zero = self.new_not(both_zero);
        let not_nan_a = self.new_not(is_nan_a);
        let not_nan_b = self.new_not(is_nan_b);
        let step1 = self.new_and(raw, not_both_zero);
        let step2 = self.new_and(step1, not_nan_a);
        self.new_and(step2, not_nan_b)
    }
    /// Assert comparison: a < b (less than)
    ///
    /// Returns a fully reified SAT variable: `result <=> fp.lt(a, b)`
    /// following IEEE-754 total-order semantics (NaN comparisons are
    /// false; -0 and +0 compare equal).
    pub fn assert_fp_lt(&mut self, a: TermId, b: TermId) -> Var {
        let fp_a = self.term_to_fp.get(&a).cloned();
        let fp_b = self.term_to_fp.get(&b).cloned();
        let result = self.sat.new_var();
        if let (Some(va), Some(vb)) = (fp_a, fp_b) {
            assert_eq!(va.format, vb.format);
            let lt = self.encode_fp_lt(&va, &vb);
            self.encode_bit_eq(result, lt);
        }
        result
    }
    /// Assert comparison: a <= b (less than or equal)
    ///
    /// Returns a fully reified SAT variable: `result <=> fp.leq(a, b)`.
    /// Defined as `not(b < a)` while neither operand is NaN, matching
    /// SMT-LIB `fp.leq` semantics (NaN comparisons are false; -0 and +0
    /// compare equal in both directions).
    pub fn assert_fp_le(&mut self, a: TermId, b: TermId) -> Var {
        let fp_a = self.term_to_fp.get(&a).cloned();
        let fp_b = self.term_to_fp.get(&b).cloned();
        let result = self.sat.new_var();
        if let (Some(va), Some(vb)) = (fp_a, fp_b) {
            assert_eq!(va.format, vb.format);
            let lt_ba = self.encode_fp_lt(&vb, &va);
            let is_nan_a = self.encode_is_nan(&va);
            let is_nan_b = self.encode_is_nan(&vb);
            let not_lt_ba = self.new_not(lt_ba);
            let not_nan_a = self.new_not(is_nan_a);
            let not_nan_b = self.new_not(is_nan_b);
            let step = self.new_and(not_lt_ba, not_nan_a);
            let le = self.new_and(step, not_nan_b);
            self.encode_bit_eq(result, le);
        }
        result
    }
    /// Convert between FP formats
    pub fn assert_fp_to_fp(&mut self, result: TermId, operand: TermId, target_format: FpFormat) {
        self.new_fp(result, target_format);
        let fp_op = self.term_to_fp.get(&operand).cloned();
        let fp_res = self.term_to_fp.get(&result).cloned();
        if let (Some(op), Some(res)) = (fp_op, fp_res) {
            if op.format == res.format {
                self.sat.add_clause([Lit::neg(res.sign), Lit::pos(op.sign)]);
                self.sat.add_clause([Lit::pos(res.sign), Lit::neg(op.sign)]);
                for (re, oe) in res.exponent.iter().zip(op.exponent.iter()) {
                    self.sat.add_clause([Lit::neg(*re), Lit::pos(*oe)]);
                    self.sat.add_clause([Lit::pos(*re), Lit::neg(*oe)]);
                }
                for (rs, os) in res.significand.iter().zip(op.significand.iter()) {
                    self.sat.add_clause([Lit::neg(*rs), Lit::pos(*os)]);
                    self.sat.add_clause([Lit::pos(*rs), Lit::neg(*os)]);
                }
            } else {
                let is_nan = self.encode_is_nan(&op);
                let is_inf = self.encode_is_infinite(&op);
                let is_zero = self.encode_is_zero(&op);
                self.sat.add_clause([Lit::neg(res.sign), Lit::pos(op.sign)]);
                self.sat.add_clause([Lit::pos(res.sign), Lit::neg(op.sign)]);
                let res_is_nan = self.encode_is_nan(&res);
                self.sat
                    .add_clause([Lit::neg(is_nan), Lit::pos(res_is_nan)]);
                let res_is_inf = self.encode_is_infinite(&res);
                self.sat
                    .add_clause([Lit::neg(is_inf), Lit::pos(res_is_inf)]);
                let res_is_zero = self.encode_is_zero(&res);
                self.sat
                    .add_clause([Lit::neg(is_zero), Lit::pos(res_is_zero)]);
            }
        }
    }
    /// Convert FP to signed integer (with rounding mode).
    ///
    /// UNSUPPORTED: a faithful bit-blasting of `fp.to_sbv` (per Z3's
    /// `fpa2bv_converter::mk_to_bv`) requires exponent-driven shifting of the
    /// significand plus rounding-mode handling that this solver does not yet
    /// encode. Rather than silently leaving the result bits unconstrained and
    /// letting the SAT model report a bogus `Sat`, we flag the solver so
    /// `check()` reports `Unknown` (never `Sat` ignoring the conversion).
    pub fn assert_fp_to_sbv(&mut self, _result: TermId, operand: TermId, width: u32) {
        let fp_op = self.term_to_fp.get(&operand).cloned();
        if let Some(_op) = fp_op {
            for _ in 0..width {
                self.sat.new_var();
            }
            self.has_unsupported_conversion = true;
        }
    }
    /// Convert FP to unsigned integer.
    ///
    /// UNSUPPORTED (see [`Self::assert_fp_to_sbv`]): the result bits are not
    /// constrained by `operand`, so the solver is flagged and `check()`
    /// reports `Unknown` instead of a bogus `Sat`.
    pub fn assert_fp_to_ubv(&mut self, _result: TermId, operand: TermId, width: u32) {
        let fp_op = self.term_to_fp.get(&operand).cloned();
        if let Some(_op) = fp_op {
            for _ in 0..width {
                self.sat.new_var();
            }
            self.has_unsupported_conversion = true;
        }
    }
    /// Convert signed integer to FP.
    ///
    /// UNSUPPORTED: a faithful `(_ to_fp ...)` from a signed bit-vector
    /// requires normalization (leading-one detection), exponent computation
    /// and rounding that this solver does not yet encode. `result` is left a
    /// fresh, unconstrained FP variable, so the solver is flagged and
    /// `check()` reports `Unknown` rather than claiming `Sat` on a model that
    /// ignores the conversion.
    pub fn assert_sbv_to_fp(
        &mut self,
        result: TermId,
        operand: TermId,
        _width: u32,
        format: FpFormat,
    ) {
        self.new_fp(result, format);
        let _ = operand;
        self.has_unsupported_conversion = true;
    }
    /// Convert unsigned integer to FP.
    ///
    /// UNSUPPORTED (see [`Self::assert_sbv_to_fp`]): `result` is unconstrained,
    /// so the solver is flagged and `check()` reports `Unknown`.
    pub fn assert_ubv_to_fp(
        &mut self,
        result: TermId,
        operand: TermId,
        _width: u32,
        format: FpFormat,
    ) {
        self.new_fp(result, format);
        let _ = operand;
        self.has_unsupported_conversion = true;
    }
    /// Convert FP to real (symbolic).
    ///
    /// UNSUPPORTED: relating an FP term to a `Real` requires cooperation with
    /// the arithmetic theory, which this module has no reference to. The
    /// conversion imposes no constraint here, so the solver is flagged and
    /// `check()` reports `Unknown` (never a bogus `Sat`).
    pub fn assert_fp_to_real(&mut self, _result: TermId, operand: TermId) {
        if self.term_to_fp.contains_key(&operand) {
            self.has_unsupported_conversion = true;
        }
    }
    /// Convert real to FP (symbolic).
    ///
    /// UNSUPPORTED (see [`Self::assert_fp_to_real`]): `result` is left a
    /// fresh, unconstrained FP variable, so the solver is flagged and
    /// `check()` reports `Unknown`.
    pub fn assert_real_to_fp(&mut self, result: TermId, _operand: TermId, format: FpFormat) {
        self.new_fp(result, format);
        self.has_unsupported_conversion = true;
    }
    /// Get the floating-point value from the model
    ///
    /// Prefers the `last_sat_model` snapshot captured at the end of the last
    /// successful `Theory::check()`, falling back to the live SAT model
    /// only when no snapshot exists yet (e.g. a direct unit test reading a
    /// value before any `check()`).
    #[must_use]
    pub fn get_value(&self, term: TermId) -> Option<FpValue> {
        let fp = self.term_to_fp.get(&term)?;
        let live = self.sat.model();
        let snapshot = &self.last_sat_model;
        let read = |var: Var| -> bool {
            let idx = var.index();
            if let Some(v) = snapshot.get(idx)
                && v.is_defined()
            {
                return v.is_true();
            }
            live.get(idx).is_some_and(|v| v.is_true())
        };
        let sign = read(fp.sign);
        let mut exponent = 0u64;
        for (i, &var) in fp.exponent.iter().enumerate() {
            if read(var) {
                exponent |= 1 << i;
            }
        }
        let mut significand = 0u64;
        for (i, &var) in fp.significand.iter().enumerate() {
            if read(var) {
                significand |= 1 << i;
            }
        }
        Some(FpValue {
            sign,
            exponent,
            significand,
            format: fp.format,
        })
    }
    /// Get all floating-point term IDs registered with this solver.
    pub fn get_interned_terms(&self) -> Vec<TermId> {
        self.term_to_fp.keys().copied().collect()
    }
    /// Check if a term is a floating-point term.
    pub fn is_fp_term(&self, term: TermId) -> bool {
        self.term_to_fp.contains_key(&term)
    }
}
impl Theory for FpSolver {
    fn id(&self) -> TheoryId {
        TheoryId::FP
    }
    fn name(&self) -> &str {
        "FP"
    }
    fn can_handle(&self, _term: TermId) -> bool {
        true
    }
    fn assert_true(&mut self, term: TermId) -> Result<TheoryResult> {
        self.assertions.push((term, true));
        Ok(TheoryResult::Sat)
    }
    fn assert_false(&mut self, term: TermId) -> Result<TheoryResult> {
        self.assertions.push((term, false));
        Ok(TheoryResult::Sat)
    }
    fn check(&mut self) -> Result<TheoryResult> {
        let committed_trail = self.sat.trail_size();
        let learned_before = self.sat.learned_clause_count();
        let mut solve_result = self.sat.solve();
        if matches!(solve_result, SolverResult::Unsat) {
            self.sat.restore_to_trail_size(committed_trail);
            self.sat.forget_learned_since(learned_before);
            solve_result = self.sat.solve();
        }
        let result = match solve_result {
            SolverResult::Sat => {
                self.last_sat_model = self.sat.model().to_vec();
                // Honesty: a `Sat` from the embedded SAT solver cannot be
                // trusted while an unsupported FP<->int/real conversion is
                // asserted, because the conversion's result bits are
                // unconstrained and the model ignores its semantics.
                if self.has_unsupported_conversion {
                    Ok(TheoryResult::Unknown)
                } else {
                    Ok(TheoryResult::Sat)
                }
            }
            SolverResult::Unsat => {
                let conflict: Vec<TermId> = if !self.assertions.is_empty() {
                    self.assertions.iter().map(|(t, _)| *t).collect()
                } else {
                    self.term_to_fp.keys().copied().collect()
                };
                Ok(TheoryResult::Unsat(conflict))
            }
            SolverResult::Unknown => Ok(TheoryResult::Unknown),
        };
        self.sat.restore_to_trail_size(committed_trail);
        self.sat.forget_learned_since(learned_before);
        result
    }
    fn push(&mut self) {
        self.context_stack
            .push((self.assertions.len(), self.has_unsupported_conversion));
        self.sat.push();
    }
    fn pop(&mut self) {
        if let Some((len, had_unsupported)) = self.context_stack.pop() {
            self.assertions.truncate(len);
            self.has_unsupported_conversion = had_unsupported;
            self.sat.pop();
        }
    }
    fn reset(&mut self) {
        self.sat.reset();
        self.term_to_fp.clear();
        self.assertions.clear();
        self.context_stack.clear();
        self.has_unsupported_conversion = false;
        self.shared_equalities.clear();
        self.equality_notifications.clear();
        self.last_sat_model.clear();
    }
    fn get_model(&self) -> Vec<(TermId, TermId)> {
        let live = self.sat.model();
        let snapshot = &self.last_sat_model;
        let model = |idx: usize| -> Option<LBool> {
            if let Some(v) = snapshot.get(idx)
                && v.is_defined()
            {
                return Some(*v);
            }
            live.get(idx).copied()
        };
        let mut value_to_terms: FxHashMap<(bool, u64, u64, u32, u32), Vec<TermId>> =
            FxHashMap::default();
        for (&term, fp_var) in &self.term_to_fp {
            let sign = model(fp_var.sign.index()).is_some_and(|v| v.is_true());
            let mut exponent = 0u64;
            for (i, &var) in fp_var.exponent.iter().enumerate() {
                if model(var.index()).is_some_and(|v| v.is_true()) {
                    exponent |= 1u64 << i;
                }
            }
            let mut significand = 0u64;
            for (i, &var) in fp_var.significand.iter().enumerate() {
                if model(var.index()).is_some_and(|v| v.is_true()) {
                    significand |= 1u64 << i;
                }
            }
            let key = (
                sign,
                exponent,
                significand,
                fp_var.format.exponent_bits,
                fp_var.format.significand_bits,
            );
            value_to_terms.entry(key).or_default().push(term);
        }
        let mut assignments = Vec::new();
        for terms in value_to_terms.values() {
            if terms.is_empty() {
                continue;
            }
            let representative = terms[0];
            for &term in terms {
                assignments.push((term, representative));
            }
        }
        assignments
    }
}
impl TheoryCombination for FpSolver {
    fn notify_equality(&mut self, eq: EqualityNotification) -> bool {
        let lhs_known = self.term_to_fp.contains_key(&eq.lhs);
        let rhs_known = self.term_to_fp.contains_key(&eq.rhs);
        if lhs_known && rhs_known {
            self.assert_fp_eq(eq.lhs, eq.rhs);
            self.equality_notifications.push(eq);
            !matches!(self.sat.solve(), SolverResult::Unsat)
        } else if lhs_known || rhs_known {
            self.equality_notifications.push(eq);
            true
        } else {
            false
        }
    }
    fn get_shared_equalities(&self) -> Vec<EqualityNotification> {
        self.shared_equalities.clone()
    }
    fn is_relevant(&self, term: TermId) -> bool {
        self.term_to_fp.contains_key(&term)
    }
}

#[cfg(test)]
mod tests;
