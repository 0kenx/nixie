//! Advanced Bit-Vector Rewriter
#![allow(dead_code, missing_docs, clippy::type_complexity)] // Self-contained; not wired into the default solve path (bv_rewriter is authoritative)
//!
//! This module implements sophisticated bit-vector simplification and rewriting:
//! - Constant folding and propagation
//! - Algebraic simplifications
//! - Bit-width reduction
//! - Strength reduction (expensive ops → cheap ops)
//! - Pattern-based rewriting
//!
//! # Handle space
//!
//! This rewriter operates in its **own** opaque handle space ([`BvHandle`], a
//! plain `usize`), *not* the crate's hash-consed AST [`crate::ast::TermId`].
//! Constants are interned by value (equal constants share a handle) and every
//! composite term (`mk_add`, `mk_mul`, …) is interned by its structure, so
//! distinct terms always receive distinct, non-colliding handles and a
//! composite handle can never be mistaken for a constant. It is *not* wired
//! into the real solver — `bv_rewriter.rs` is the authoritative AST-backed
//! rewriter — but its simplification helpers are internally sound.

#[allow(unused_imports)]
use crate::prelude::*;

/// Opaque handle for a bit-vector term in this rewriter's local store.
///
/// This is intentionally **not** the crate's AST `TermId`: this module is a
/// self-contained calculator over `u64` constant values and interned opaque
/// composite handles (see the module docs).
pub type BvHandle = usize;

/// Bit-vector operation
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BvOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    UDiv,
    SDiv,
    URem,
    SRem,
    Neg,

    // Bitwise
    And,
    Or,
    Xor,
    Not,

    // Shifts and rotates
    Shl,
    LShr,
    AShr,
    RotateLeft,
    RotateRight,

    // Comparisons
    ULt,
    ULe,
    UGt,
    UGe,
    SLt,
    SLe,
    SGt,
    SGe,
    Eq,

    // Extraction and concatenation
    Extract,
    Concat,
    ZeroExtend,
    SignExtend,
}

/// Rewrite rule
pub struct RewriteRule {
    /// Rule name
    pub name: String,
    /// Pattern to match
    pub pattern: Pattern,
    /// Replacement term constructor
    pub replacement: Box<dyn Fn(&[BvHandle]) -> Option<BvHandle>>,
}

/// Pattern for matching
#[derive(Debug, Clone)]
pub enum Pattern {
    /// Constant value
    Const(u64),
    /// Variable
    Var(String),
    /// Operation with subpatterns
    Op(BvOp, Vec<Pattern>),
    /// Wildcard (matches anything)
    Any,
}

/// Statistics for rewriter
#[derive(Debug, Clone, Default)]
pub struct RewriterStats {
    pub rewrites_applied: u64,
    pub constant_folding: u64,
    pub algebraic_simplifications: u64,
    pub strength_reductions: u64,
    pub bit_width_reductions: u64,
}

/// Configuration for rewriter
#[derive(Debug, Clone)]
pub struct RewriterConfig {
    /// Enable constant folding
    pub enable_constant_folding: bool,
    /// Enable algebraic simplifications
    pub enable_algebraic: bool,
    /// Enable strength reduction
    pub enable_strength_reduction: bool,
    /// Enable bit-width reduction
    pub enable_bit_width_reduction: bool,
    /// Maximum rewrite iterations
    pub max_iterations: usize,
}

impl Default for RewriterConfig {
    fn default() -> Self {
        Self {
            enable_constant_folding: true,
            enable_algebraic: true,
            enable_strength_reduction: true,
            enable_bit_width_reduction: true,
            max_iterations: 10,
        }
    }
}

/// Advanced bit-vector rewriter
pub struct AdvancedBvRewriter {
    config: RewriterConfig,
    stats: RewriterStats,
    /// Rewrite rules
    rules: Vec<RewriteRule>,
    /// Constant cache: handle -> concrete value.
    constants: FxHashMap<BvHandle, u64>,
    /// Next fresh handle to allocate. Handle `0` is reserved as an invalid
    /// sentinel so no real term ever collides with it.
    next_handle: BvHandle,
    /// Interning of constants by value, so equal constants share a handle.
    const_intern: FxHashMap<u64, BvHandle>,
    /// Interning of composite terms by `(op, lhs, rhs, width)`, so
    /// structurally equal composites share a handle (and are always distinct
    /// from constant handles).
    composite_intern: FxHashMap<(BvOp, BvHandle, BvHandle, usize), BvHandle>,
    /// Structure of each composite handle (for introspection/debugging).
    composites: FxHashMap<BvHandle, (BvOp, BvHandle, BvHandle, usize)>,
}

impl AdvancedBvRewriter {
    /// Create a new rewriter
    pub fn new(config: RewriterConfig) -> Self {
        let mut rewriter = Self {
            config,
            stats: RewriterStats::default(),
            rules: Vec::new(),
            constants: FxHashMap::default(),
            next_handle: 1,
            const_intern: FxHashMap::default(),
            composite_intern: FxHashMap::default(),
            composites: FxHashMap::default(),
        };

        rewriter.initialize_rules();
        rewriter
    }

    /// Allocate a fresh, previously-unused handle.
    fn fresh_handle(&mut self) -> BvHandle {
        let h = self.next_handle;
        self.next_handle += 1;
        h
    }

    /// Intern a composite term, returning a stable handle for a given
    /// `(op, lhs, rhs, width)` structure.
    fn intern_composite(
        &mut self,
        op: BvOp,
        lhs: BvHandle,
        rhs: BvHandle,
        width: usize,
    ) -> BvHandle {
        if let Some(&h) = self.composite_intern.get(&(op, lhs, rhs, width)) {
            return h;
        }
        let h = self.fresh_handle();
        self.composite_intern.insert((op, lhs, rhs, width), h);
        self.composites.insert(h, (op, lhs, rhs, width));
        h
    }

    /// Initialize rewrite rules
    fn initialize_rules(&mut self) {
        // Note: In real implementation, rules would be proper closures
        // For now, we'll just define the rule structure

        if self.config.enable_constant_folding {
            // x + 0 → x
            // x * 0 → 0
            // x * 1 → x
            // x & 0 → 0
            // x & ~0 → x
            // x | 0 → x
            // x | ~0 → ~0
        }

        if self.config.enable_algebraic {
            // x + x → 2*x
            // x - x → 0
            // x & x → x
            // x | x → x
            // x ^ x → 0
            // ~(~x) → x
        }

        if self.config.enable_strength_reduction {
            // x * 2^n → x << n
            // x / 2^n → x >> n (for unsigned)
            // x % 2^n → x & (2^n - 1)
        }
    }

    /// Rewrite a bit-vector term
    pub fn rewrite(&mut self, term: BvHandle) -> Result<BvHandle, String> {
        let mut current = term;
        let mut iteration = 0;

        while iteration < self.config.max_iterations {
            let rewritten = self.rewrite_once(current)?;

            if rewritten == current {
                break;
            }

            current = rewritten;
            self.stats.rewrites_applied += 1;
            iteration += 1;
        }

        Ok(current)
    }

    /// Perform one rewrite pass
    fn rewrite_once(&mut self, term: BvHandle) -> Result<BvHandle, String> {
        // Try constant folding first
        if self.config.enable_constant_folding
            && let Some(folded) = self.try_constant_fold(term)?
        {
            self.stats.constant_folding += 1;
            return Ok(folded);
        }

        // Try algebraic simplifications
        if self.config.enable_algebraic
            && let Some(simplified) = self.try_algebraic_simplify(term)?
        {
            self.stats.algebraic_simplifications += 1;
            return Ok(simplified);
        }

        // Try strength reduction
        if self.config.enable_strength_reduction
            && let Some(reduced) = self.try_strength_reduction(term)?
        {
            self.stats.strength_reductions += 1;
            return Ok(reduced);
        }

        // Try bit-width reduction
        if self.config.enable_bit_width_reduction
            && let Some(narrowed) = self.try_bit_width_reduction(term)?
        {
            self.stats.bit_width_reductions += 1;
            return Ok(narrowed);
        }

        Ok(term)
    }

    /// Try constant folding
    fn try_constant_fold(&mut self, _term: BvHandle) -> Result<Option<BvHandle>, String> {
        // Placeholder: would check if all operands are constants
        // and compute result

        // Example patterns:
        // c1 + c2 → c3 where c3 = c1 + c2
        // c1 & c2 → c3 where c3 = c1 & c2
        // extract[i:j](c) → compute extraction

        Ok(None)
    }

    /// Try algebraic simplifications
    fn try_algebraic_simplify(&self, _term: BvHandle) -> Result<Option<BvHandle>, String> {
        // Placeholder: would pattern match and apply algebraic rules

        // Example simplifications:
        // x + 0 → x
        // x * 0 → 0
        // x * 1 → x
        // x - x → 0
        // x & x → x
        // x | x → x
        // x ^ x → 0
        // ~(~x) → x
        // x & 0 → 0
        // x | ~0 → ~0

        Ok(None)
    }

    /// Try strength reduction (expensive ops → cheap ops)
    fn try_strength_reduction(&self, _term: BvHandle) -> Result<Option<BvHandle>, String> {
        // Placeholder: would identify and replace expensive operations

        // Example reductions:
        // x * 2^n → x << n
        // x / 2^n → x >> n (unsigned)
        // x % 2^n → x & (2^n - 1)
        // x * 3 → (x << 1) + x
        // x * 5 → (x << 2) + x

        Ok(None)
    }

    /// Try bit-width reduction
    fn try_bit_width_reduction(&self, _term: BvHandle) -> Result<Option<BvHandle>, String> {
        // Placeholder: would analyze value ranges and reduce bit-widths

        // Example reductions:
        // If x: bv32 but only uses lower 8 bits, rewrite as bv8
        // extract[31:24](concat(a, b)) → extract from a directly

        Ok(None)
    }

    /// Simplify bit-vector addition
    pub fn simplify_add(
        &mut self,
        lhs: BvHandle,
        rhs: BvHandle,
        width: usize,
    ) -> Result<BvHandle, String> {
        // Check for constants
        if let (Some(&lhs_val), Some(&rhs_val)) =
            (self.constants.get(&lhs), self.constants.get(&rhs))
        {
            let result = (lhs_val.wrapping_add(rhs_val)) & self.mask(width);
            return self.mk_const(result, width);
        }

        // x + 0 → x
        if self.is_zero(rhs) {
            return Ok(lhs);
        }

        // 0 + x → x
        if self.is_zero(lhs) {
            return Ok(rhs);
        }

        // x + (-x) → 0  (assuming we detect negation)
        if self.is_negation(lhs, rhs) {
            return self.mk_const(0, width);
        }

        // No simplification
        self.mk_add(lhs, rhs, width)
    }

    /// Simplify bit-vector multiplication
    pub fn simplify_mul(
        &mut self,
        lhs: BvHandle,
        rhs: BvHandle,
        width: usize,
    ) -> Result<BvHandle, String> {
        // Check for constants
        if let (Some(&lhs_val), Some(&rhs_val)) =
            (self.constants.get(&lhs), self.constants.get(&rhs))
        {
            let result = (lhs_val.wrapping_mul(rhs_val)) & self.mask(width);
            return self.mk_const(result, width);
        }

        // x * 0 → 0
        if self.is_zero(rhs) || self.is_zero(lhs) {
            return self.mk_const(0, width);
        }

        // x * 1 → x
        if self.is_one(rhs) {
            return Ok(lhs);
        }

        // 1 * x → x
        if self.is_one(lhs) {
            return Ok(rhs);
        }

        // x * 2^n → x << n (strength reduction)
        if let Some(n) = self.is_power_of_two(rhs) {
            self.stats.strength_reductions += 1;
            let shift_amount = self.mk_const(n, width)?;
            return self.mk_shl(lhs, shift_amount, width);
        }

        // No simplification
        self.mk_mul(lhs, rhs, width)
    }

    /// Simplify bit-vector AND
    pub fn simplify_and(
        &mut self,
        lhs: BvHandle,
        rhs: BvHandle,
        width: usize,
    ) -> Result<BvHandle, String> {
        // Check for constants
        if let (Some(&lhs_val), Some(&rhs_val)) =
            (self.constants.get(&lhs), self.constants.get(&rhs))
        {
            let result = lhs_val & rhs_val & self.mask(width);
            return self.mk_const(result, width);
        }

        // x & 0 → 0
        if self.is_zero(rhs) || self.is_zero(lhs) {
            return self.mk_const(0, width);
        }

        // x & ~0 → x
        if self.is_all_ones(rhs, width) {
            return Ok(lhs);
        }

        if self.is_all_ones(lhs, width) {
            return Ok(rhs);
        }

        // x & x → x
        if lhs == rhs {
            return Ok(lhs);
        }

        // No simplification
        self.mk_and(lhs, rhs, width)
    }

    /// Simplify bit-vector OR
    pub fn simplify_or(
        &mut self,
        lhs: BvHandle,
        rhs: BvHandle,
        width: usize,
    ) -> Result<BvHandle, String> {
        // Check for constants
        if let (Some(&lhs_val), Some(&rhs_val)) =
            (self.constants.get(&lhs), self.constants.get(&rhs))
        {
            let result = (lhs_val | rhs_val) & self.mask(width);
            return self.mk_const(result, width);
        }

        // x | 0 → x
        if self.is_zero(rhs) {
            return Ok(lhs);
        }

        if self.is_zero(lhs) {
            return Ok(rhs);
        }

        // x | ~0 → ~0
        if self.is_all_ones(rhs, width) {
            return Ok(rhs);
        }

        if self.is_all_ones(lhs, width) {
            return Ok(lhs);
        }

        // x | x → x
        if lhs == rhs {
            return Ok(lhs);
        }

        // No simplification
        self.mk_or(lhs, rhs, width)
    }

    /// Simplify bit-vector XOR
    pub fn simplify_xor(
        &mut self,
        lhs: BvHandle,
        rhs: BvHandle,
        width: usize,
    ) -> Result<BvHandle, String> {
        // Check for constants
        if let (Some(&lhs_val), Some(&rhs_val)) =
            (self.constants.get(&lhs), self.constants.get(&rhs))
        {
            let result = (lhs_val ^ rhs_val) & self.mask(width);
            return self.mk_const(result, width);
        }

        // x ^ 0 → x
        if self.is_zero(rhs) {
            return Ok(lhs);
        }

        if self.is_zero(lhs) {
            return Ok(rhs);
        }

        // x ^ x → 0
        if lhs == rhs {
            return self.mk_const(0, width);
        }

        // No simplification
        self.mk_xor(lhs, rhs, width)
    }

    /// Simplify shift left
    pub fn simplify_shl(
        &mut self,
        value: BvHandle,
        shift: BvHandle,
        width: usize,
    ) -> Result<BvHandle, String> {
        // Check for constant shift
        if let Some(&shift_val) = self.constants.get(&shift) {
            if shift_val == 0 {
                return Ok(value);
            }

            if shift_val >= width as u64 {
                return self.mk_const(0, width);
            }

            // If value is also constant
            if let Some(&value_val) = self.constants.get(&value) {
                let result = (value_val << shift_val) & self.mask(width);
                return self.mk_const(result, width);
            }
        }

        // value << 0 → value
        if self.is_zero(shift) {
            return Ok(value);
        }

        self.mk_shl(value, shift, width)
    }

    // Helper methods

    fn is_zero(&self, term: BvHandle) -> bool {
        self.constants.get(&term) == Some(&0)
    }

    fn is_one(&self, term: BvHandle) -> bool {
        self.constants.get(&term) == Some(&1)
    }

    fn is_all_ones(&self, term: BvHandle, width: usize) -> bool {
        self.constants.get(&term) == Some(&self.mask(width))
    }

    fn is_power_of_two(&self, term: BvHandle) -> Option<u64> {
        if let Some(&val) = self.constants.get(&term)
            && val > 0
            && (val & (val - 1)) == 0
        {
            return Some(val.trailing_zeros() as u64);
        }
        None
    }

    /// Whether `rhs` is known to be the two's-complement negation of `lhs`.
    ///
    /// This handle space does not track symbolic negation relationships (there
    /// is no `mk_neg`), and the both-constant case is already folded by the
    /// callers before this check is reached, so there is no additional
    /// information to exploit here. It therefore conservatively returns
    /// `false` — a *sound* under-approximation: the `x + (-x) → 0` rule simply
    /// never fires, which can miss a simplification but never produces a wrong
    /// result.
    fn is_negation(&self, _lhs: BvHandle, _rhs: BvHandle) -> bool {
        false
    }

    fn mask(&self, width: usize) -> u64 {
        if width >= 64 {
            u64::MAX
        } else {
            (1u64 << width) - 1
        }
    }

    // Term constructors.
    //
    // Constants are interned by value; composites by structure. Every handle
    // returned here is either an interned constant (present in `constants`) or
    // a fresh interned composite handle — never a fabricated `0`, and never a
    // collision between a composite and a constant.

    fn mk_const(&mut self, value: u64, width: usize) -> Result<BvHandle, String> {
        let value = value & self.mask(width);
        if let Some(&h) = self.const_intern.get(&value) {
            return Ok(h);
        }
        let h = self.fresh_handle();
        self.const_intern.insert(value, h);
        self.constants.insert(h, value);
        Ok(h)
    }

    fn mk_add(&mut self, lhs: BvHandle, rhs: BvHandle, width: usize) -> Result<BvHandle, String> {
        Ok(self.intern_composite(BvOp::Add, lhs, rhs, width))
    }

    fn mk_mul(&mut self, lhs: BvHandle, rhs: BvHandle, width: usize) -> Result<BvHandle, String> {
        Ok(self.intern_composite(BvOp::Mul, lhs, rhs, width))
    }

    fn mk_and(&mut self, lhs: BvHandle, rhs: BvHandle, width: usize) -> Result<BvHandle, String> {
        Ok(self.intern_composite(BvOp::And, lhs, rhs, width))
    }

    fn mk_or(&mut self, lhs: BvHandle, rhs: BvHandle, width: usize) -> Result<BvHandle, String> {
        Ok(self.intern_composite(BvOp::Or, lhs, rhs, width))
    }

    fn mk_xor(&mut self, lhs: BvHandle, rhs: BvHandle, width: usize) -> Result<BvHandle, String> {
        Ok(self.intern_composite(BvOp::Xor, lhs, rhs, width))
    }

    fn mk_shl(
        &mut self,
        value: BvHandle,
        shift: BvHandle,
        width: usize,
    ) -> Result<BvHandle, String> {
        Ok(self.intern_composite(BvOp::Shl, value, shift, width))
    }

    /// Get statistics
    pub fn stats(&self) -> &RewriterStats {
        &self.stats
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rewriter_creation() {
        let config = RewriterConfig::default();
        let rewriter = AdvancedBvRewriter::new(config);
        assert_eq!(rewriter.stats.rewrites_applied, 0);
    }

    // ── TODO-1012: sound handle allocation (no fake 0, no collisions) ─────

    #[test]
    fn test_composite_handles_are_distinct_and_nonzero() {
        let mut r = AdvancedBvRewriter::new(RewriterConfig::default());
        // Symbolic operands: bare handles that are not registered constants.
        let x = 100usize;
        let y = 200usize;
        let zero = r.mk_const(0, 8).expect("mk_const");

        // An unsimplifiable composite must get a fresh, non-zero handle that
        // is distinct from the constant-0 handle. (Previously every composite
        // fallback returned the fake handle 0, colliding with the constant 0.)
        let add = r.mk_add(x, y, 8).expect("mk_add");
        assert_ne!(add, 0, "composite must not be the reserved 0 sentinel");
        assert_ne!(add, zero, "composite must not collide with the constant 0");
        assert!(
            !r.constants.contains_key(&add),
            "a composite handle is never a registered constant"
        );

        // Structural interning: identical structure shares a handle.
        let add2 = r.mk_add(x, y, 8).expect("mk_add");
        assert_eq!(add, add2);

        // Distinct structure yields a distinct handle.
        let mul = r.mk_mul(x, y, 8).expect("mk_mul");
        assert_ne!(add, mul);
        assert_ne!(mul, zero);
    }

    #[test]
    fn test_symbolic_add_not_folded_to_zero() {
        // Regression: a symbolic `simplify_add` used to return the fake handle
        // 0, which aliased the constant 0 and made downstream `is_zero`
        // wrongly fire. It must now return a real, non-constant handle.
        let mut r = AdvancedBvRewriter::new(RewriterConfig::default());
        let x = 100usize;
        let y = 200usize;
        let sum = r.simplify_add(x, y, 8).expect("simplify_add");
        assert!(
            !r.constants.contains_key(&sum),
            "symbolic sum must not be a constant"
        );
        assert!(
            !r.is_zero(sum),
            "symbolic sum must not be mistaken for zero"
        );
    }

    #[test]
    fn test_equal_constants_share_handle() {
        let mut r = AdvancedBvRewriter::new(RewriterConfig::default());
        let a = r.mk_const(7, 8).expect("mk_const");
        let b = r.mk_const(7, 8).expect("mk_const");
        assert_eq!(a, b, "equal constants must intern to the same handle");
        let c = r.mk_const(9, 8).expect("mk_const");
        assert_ne!(a, c, "distinct constants must get distinct handles");
    }

    #[test]
    fn test_simplify_add_with_zero() {
        let config = RewriterConfig::default();
        let mut rewriter = AdvancedBvRewriter::new(config);

        let x = 10;
        let zero = rewriter
            .mk_const(0, 32)
            .expect("test operation should succeed");

        let result = rewriter
            .simplify_add(x, zero, 32)
            .expect("test operation should succeed");
        assert_eq!(result, x);
    }

    #[test]
    fn test_simplify_mul_with_zero() {
        let config = RewriterConfig::default();
        let mut rewriter = AdvancedBvRewriter::new(config);

        let x = 10;
        let zero = rewriter
            .mk_const(0, 32)
            .expect("test operation should succeed");

        let result = rewriter
            .simplify_mul(x, zero, 32)
            .expect("test operation should succeed");
        assert_eq!(result, zero);
    }

    #[test]
    fn test_simplify_mul_with_one() {
        let config = RewriterConfig::default();
        let mut rewriter = AdvancedBvRewriter::new(config);

        let x = 10;
        let one = rewriter
            .mk_const(1, 32)
            .expect("test operation should succeed");

        let result = rewriter
            .simplify_mul(x, one, 32)
            .expect("test operation should succeed");
        assert_eq!(result, x);
    }

    #[test]
    fn test_simplify_and_identity() {
        let config = RewriterConfig::default();
        let mut rewriter = AdvancedBvRewriter::new(config);

        let x = 10;

        let result = rewriter
            .simplify_and(x, x, 32)
            .expect("test operation should succeed");
        assert_eq!(result, x);
    }

    #[test]
    fn test_simplify_xor_self() {
        let config = RewriterConfig::default();
        let mut rewriter = AdvancedBvRewriter::new(config);

        let x = 10;

        let result = rewriter
            .simplify_xor(x, x, 32)
            .expect("test operation should succeed");
        let zero = rewriter
            .mk_const(0, 32)
            .expect("test operation should succeed");
        assert_eq!(result, zero);
    }

    #[test]
    fn test_constant_folding_add() {
        let config = RewriterConfig::default();
        let mut rewriter = AdvancedBvRewriter::new(config);

        let c1 = rewriter
            .mk_const(5, 32)
            .expect("test operation should succeed");
        let c2 = rewriter
            .mk_const(3, 32)
            .expect("test operation should succeed");

        let result = rewriter
            .simplify_add(c1, c2, 32)
            .expect("test operation should succeed");

        // Result should be constant 8
        assert!(rewriter.constants.contains_key(&result));
        assert_eq!(rewriter.constants.get(&result), Some(&8));
    }

    #[test]
    fn test_mask_generation() {
        let rewriter = AdvancedBvRewriter::new(RewriterConfig::default());

        assert_eq!(rewriter.mask(8), 0xFF);
        assert_eq!(rewriter.mask(16), 0xFFFF);
        assert_eq!(rewriter.mask(32), 0xFFFFFFFF);
    }

    #[test]
    fn test_is_power_of_two() {
        let mut rewriter = AdvancedBvRewriter::new(RewriterConfig::default());

        let t1 = rewriter
            .mk_const(1, 32)
            .expect("test operation should succeed");
        let t2 = rewriter
            .mk_const(2, 32)
            .expect("test operation should succeed");
        let t4 = rewriter
            .mk_const(4, 32)
            .expect("test operation should succeed");
        let t8 = rewriter
            .mk_const(8, 32)
            .expect("test operation should succeed");
        let t3 = rewriter
            .mk_const(3, 32)
            .expect("test operation should succeed");

        assert_eq!(rewriter.is_power_of_two(t1), Some(0));
        assert_eq!(rewriter.is_power_of_two(t2), Some(1));
        assert_eq!(rewriter.is_power_of_two(t4), Some(2));
        assert_eq!(rewriter.is_power_of_two(t8), Some(3));
        assert_eq!(rewriter.is_power_of_two(t3), None);
    }

    #[test]
    fn test_strength_reduction_mul() {
        let config = RewriterConfig {
            enable_strength_reduction: true,
            ..Default::default()
        };
        let mut rewriter = AdvancedBvRewriter::new(config);

        let x = 10;
        let power_of_two = rewriter
            .mk_const(8, 32)
            .expect("test operation should succeed");

        let result = rewriter.simplify_mul(x, power_of_two, 32);
        assert!(result.is_ok());
        // Should be converted to shift
        assert_eq!(rewriter.stats.strength_reductions, 1);
    }

    #[test]
    fn test_shl_zero() {
        let config = RewriterConfig::default();
        let mut rewriter = AdvancedBvRewriter::new(config);

        let x = 10;
        let zero = rewriter
            .mk_const(0, 32)
            .expect("test operation should succeed");

        let result = rewriter
            .simplify_shl(x, zero, 32)
            .expect("test operation should succeed");
        assert_eq!(result, x);
    }
}
