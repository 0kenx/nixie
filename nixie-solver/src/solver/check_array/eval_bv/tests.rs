//! Characterisation and equivalence tests for [`Solver::evaluate_bv_expr`].
//!
//! The evaluator answers the array cross-theory check on *input-shaped* terms,
//! so its exact answer on every arm – including the width-mismatch rejections
//! and the total division/shift cases – is load bearing: a value that is off by
//! one bit turns a satisfiable formula into a reported conflict.  Every arm is
//! pinned here by value, and the whole corpus is pinned by digest.

use super::Solver;
use crate::prelude::*;
use nixie_core::ast::{TermId, TermKind, TermManager};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use smallvec::smallvec;

/// A bound bit-vector variable environment, as `collect_bv_var_equalities`
/// builds it.
type Bindings = FxHashMap<TermId, (BigInt, u32)>;

/// A scratch term manager plus the variable bindings the evaluator reads.
struct Env {
    manager: TermManager,
    bindings: Bindings,
    solver: Solver,
}

impl Env {
    fn new() -> Self {
        Self {
            manager: TermManager::new(),
            bindings: Bindings::default(),
            solver: Solver::new(),
        }
    }

    /// A bit-vector literal of `width` bits.
    fn constant(&mut self, value: i64, width: u32) -> TermId {
        self.manager.mk_bitvec(value, width)
    }

    /// A bit-vector literal from a `BigInt`, for values past `i64`.
    fn big_constant(&mut self, value: BigInt, width: u32) -> TermId {
        self.manager.mk_bitvec(value, width)
    }

    /// A variable bound to `(value, width)` in the environment.
    fn bound_var(&mut self, name: &str, value: i64, width: u32) -> TermId {
        let sort = self.manager.sorts.bitvec(width);
        let var = self.manager.mk_var(name, sort);
        self.bindings.insert(var, (BigInt::from(value), width));
        var
    }

    /// A variable with no binding – the evaluator must give up on it.
    fn free_var(&mut self, name: &str, width: u32) -> TermId {
        let sort = self.manager.sorts.bitvec(width);
        self.manager.mk_var(name, sort)
    }

    /// Intern `kind` *without* the builder's constant folding, so the evaluator
    /// is the only thing that ever computes a value.  The node's own sort is
    /// irrelevant to the evaluator (it reads widths off operand *values*), and
    /// is taken from `width` purely so the corpus is well formed.
    fn node(&mut self, kind: TermKind, width: u32) -> TermId {
        let sort = self.manager.sorts.bitvec(width);
        self.manager.intern_term(kind, sort)
    }

    /// The width the node built from `operand` should carry.
    ///
    /// The fallback is reached only for the corpus's non-bit-vector poison
    /// leaf, whose parent node's sort the evaluator never reads – it takes
    /// widths off operand *values*, not off the node.
    fn width_of(&self, operand: TermId) -> u32 {
        self.manager
            .get(operand)
            .and_then(|t| self.manager.sorts.get(t.sort))
            .and_then(|s| s.bitvec_width())
            .unwrap_or(8)
    }

    fn eval(&self, term: TermId) -> Option<(BigInt, u32)> {
        self.solver
            .evaluate_bv_expr(term, &self.bindings, &self.manager)
    }

    /// `eval`, rendered for comparison: `Some((value, width))` as `value/width`.
    fn rendered(&self, term: TermId) -> String {
        match self.eval(term) {
            None => "-".to_string(),
            Some((value, width)) => format!("{value}/{width}"),
        }
    }
}

/// `Some((value, width))` with an `i64` literal, for terse assertions.
fn val(value: i64, width: u32) -> Option<(BigInt, u32)> {
    Some((BigInt::from(value), width))
}

/// `2^width - 1`.
fn all_ones(width: u32) -> BigInt {
    (BigInt::one() << width as usize) - BigInt::one()
}

// ======== Leaves ========

/// A literal evaluates to itself, carrying its own declared width.
#[test]
fn literal_carries_its_width() {
    let mut env = Env::new();
    let eight = env.constant(5, 8);
    let four = env.constant(5, 4);
    assert_eq!(env.eval(eight), val(5, 8));
    assert_eq!(env.eval(four), val(5, 4));
}

/// A bound variable takes the environment's value *and* the environment's
/// width, which need not agree with the variable's sort.
#[test]
fn bound_variable_takes_the_environment_width() {
    let mut env = Env::new();
    let x = env.bound_var("x", 9, 8);
    assert_eq!(env.eval(x), val(9, 8));
}

/// An unbound variable is not evaluable – never a defaulted zero.
#[test]
fn free_variable_is_not_evaluable() {
    let mut env = Env::new();
    let x = env.free_var("x", 8);
    assert_eq!(env.eval(x), None);
}

/// Every `TermKind` of *bit-vector* sort folds; what is left over is reported
/// as *not evaluable*, never as a defaulted value.
///
/// The four bit-vector comparisons are Boolean-sorted predicates, not
/// bit-vector expressions, and `select` is an array read with no model here.
/// The `ite` in this list has a *bit-vector* condition, which is not a condition
/// at all – `ite` with a genuine Boolean condition folds, and has its own tests.
#[test]
fn non_bitvector_kinds_are_not_evaluable() {
    let mut env = Env::new();
    let a = env.constant(6, 8);
    let b = env.constant(3, 8);
    let unhandled = [
        TermKind::BvUlt(a, b),
        TermKind::BvUle(a, b),
        TermKind::BvSlt(a, b),
        TermKind::BvSle(a, b),
        TermKind::Ite(a, a, b),
        TermKind::Select(a, b),
    ];
    for kind in unhandled {
        let term = env.node(kind, 8);
        assert_eq!(env.eval(term), None, "expected no value for {term:?}");
    }
    let int = env.manager.mk_int(7);
    assert_eq!(env.eval(int), None);
    let boolean = env.manager.mk_true();
    assert_eq!(env.eval(boolean), None);
}

/// Every bit-vector-sorted `TermKind` has an arm.
///
/// A regression guard for the five kinds that had none before this evaluator
/// delegated to `bv_fold`: each one previously answered *not evaluable*, and
/// each answers with a value now.
#[test]
fn every_bitvector_kind_folds() {
    let mut env = Env::new();
    let a = env.constant(6, 8);
    let b = env.constant(3, 8);
    let kinds = [
        TermKind::BvAdd(a, b),
        TermKind::BvSub(a, b),
        TermKind::BvMul(a, b),
        TermKind::BvUdiv(a, b),
        TermKind::BvUrem(a, b),
        TermKind::BvSdiv(a, b),
        TermKind::BvSrem(a, b),
        TermKind::BvAnd(a, b),
        TermKind::BvOr(a, b),
        TermKind::BvXor(a, b),
        TermKind::BvShl(a, b),
        TermKind::BvLshr(a, b),
        TermKind::BvAshr(a, b),
        TermKind::BvConcat(a, b),
        TermKind::BvNot(a),
        TermKind::BvExtract {
            high: 3,
            low: 0,
            arg: a,
        },
    ];
    for kind in kinds {
        let term = env.node(kind, 8);
        assert!(env.eval(term).is_some(), "expected a value for {term:?}");
    }
}

// ======== Width propagation ========

/// Every width-checked binary op refuses mismatched operand widths outright
/// rather than picking one of the two widths.
#[test]
fn width_mismatch_is_refused_by_the_width_checked_ops() {
    let mut env = Env::new();
    let wide = env.constant(3, 8);
    let narrow = env.constant(3, 4);
    let checked = [
        TermKind::BvAdd(wide, narrow),
        TermKind::BvSub(wide, narrow),
        TermKind::BvMul(wide, narrow),
        TermKind::BvUdiv(wide, narrow),
        TermKind::BvUrem(wide, narrow),
        TermKind::BvAnd(wide, narrow),
        TermKind::BvOr(wide, narrow),
        TermKind::BvXor(wide, narrow),
    ];
    for kind in checked {
        let term = env.node(kind, 8);
        assert_eq!(env.eval(term), None, "expected no value for {term:?}");
    }
}

/// The shifts are the exception: they take their width from the *shifted*
/// operand and never look at the distance's width.  `(bvshl #x03:8 #b0001:4)`
/// is not well sorted SMT-LIB, but the evaluator answers it, and that answer is
/// what the cross-theory check has always compared against.
#[test]
fn shifts_ignore_the_distance_width() {
    let mut env = Env::new();
    let value = env.constant(3, 8);
    let distance = env.constant(1, 4);
    let shl = env.node(TermKind::BvShl(value, distance), 8);
    let lshr = env.node(TermKind::BvLshr(value, distance), 8);
    assert_eq!(env.eval(shl), val(6, 8));
    assert_eq!(env.eval(lshr), val(1, 8));
}

/// A binary op reports the *left* operand's width, and a mismatch inside a
/// nested term aborts the whole evaluation rather than the failing subterm.
#[test]
fn a_mismatch_deep_inside_aborts_the_whole_term() {
    let mut env = Env::new();
    let wide = env.constant(3, 8);
    let narrow = env.constant(3, 4);
    let bad = env.node(TermKind::BvAdd(wide, narrow), 8);
    let outer = env.node(TermKind::BvAdd(bad, wide), 8);
    assert_eq!(env.eval(outer), None);
}

// ======== Arithmetic ========

/// `bvadd` wraps modulo `2^width`.
#[test]
fn add_wraps() {
    let mut env = Env::new();
    let a = env.constant(200, 8);
    let b = env.constant(100, 8);
    let sum = env.node(TermKind::BvAdd(a, b), 8);
    assert_eq!(env.eval(sum), val(44, 8));
}

/// `bvsub` wraps modulo `2^width` and never yields a negative value –
/// `0 - 1` is all-ones, not `-1`.
#[test]
fn sub_wraps_without_going_negative() {
    let mut env = Env::new();
    let zero = env.constant(0, 8);
    let one = env.constant(1, 8);
    let diff = env.node(TermKind::BvSub(zero, one), 8);
    assert_eq!(env.eval(diff), Some((all_ones(8), 8)));

    // Two full wraps down: still in range.
    let big = env.constant(255, 8);
    let twice = env.node(TermKind::BvSub(diff, big), 8);
    assert_eq!(env.eval(twice), val(0, 8));
}

/// `bvmul` wraps modulo `2^width`.
#[test]
fn mul_wraps() {
    let mut env = Env::new();
    let a = env.constant(16, 8);
    let b = env.constant(17, 8);
    let product = env.node(TermKind::BvMul(a, b), 8);
    assert_eq!(env.eval(product), val(16, 8));
}

/// `bvudiv` is total: division by zero is the all-ones vector, per SMT-LIB.
#[test]
fn udiv_by_zero_is_all_ones() {
    let mut env = Env::new();
    let a = env.constant(7, 8);
    let zero = env.constant(0, 8);
    let quotient = env.node(TermKind::BvUdiv(a, zero), 8);
    assert_eq!(env.eval(quotient), Some((all_ones(8), 8)));

    let three = env.constant(3, 8);
    let exact = env.node(TermKind::BvUdiv(a, three), 8);
    assert_eq!(env.eval(exact), val(2, 8));
}

/// `bvudiv` is *unsigned*: the top-bit-set operand is a large positive number,
/// not a negative one.  `#xFF / #x02` is `127`, not `0`.
#[test]
fn udiv_is_unsigned() {
    let mut env = Env::new();
    let minus_one = env.constant(255, 8);
    let two = env.constant(2, 8);
    let quotient = env.node(TermKind::BvUdiv(minus_one, two), 8);
    assert_eq!(env.eval(quotient), val(127, 8));
}

/// `bvurem` is total: remainder by zero is the left operand, per SMT-LIB.
#[test]
fn urem_by_zero_is_the_dividend() {
    let mut env = Env::new();
    let a = env.constant(7, 8);
    let zero = env.constant(0, 8);
    let remainder = env.node(TermKind::BvUrem(a, zero), 8);
    assert_eq!(env.eval(remainder), val(7, 8));

    let three = env.constant(3, 8);
    let proper = env.node(TermKind::BvUrem(a, three), 8);
    assert_eq!(env.eval(proper), val(1, 8));
}

/// The extreme unsigned values divide and remainder without wrapping into
/// range violations: `#xFF / #xFF = 1`, `#xFF % #xFF = 0`.
#[test]
fn division_extremes_stay_in_range() {
    let mut env = Env::new();
    let top = env.constant(255, 8);
    let quotient = env.node(TermKind::BvUdiv(top, top), 8);
    let remainder = env.node(TermKind::BvUrem(top, top), 8);
    assert_eq!(env.eval(quotient), val(1, 8));
    assert_eq!(env.eval(remainder), val(0, 8));
}

// ======== Bitwise ========

/// `bvand` / `bvor` / `bvxor` are bitwise within the width.
#[test]
fn bitwise_ops() {
    let mut env = Env::new();
    let a = env.constant(0b1100, 8);
    let b = env.constant(0b1010, 8);
    let and = env.node(TermKind::BvAnd(a, b), 8);
    let or = env.node(TermKind::BvOr(a, b), 8);
    let xor = env.node(TermKind::BvXor(a, b), 8);
    assert_eq!(env.eval(and), val(0b1000, 8));
    assert_eq!(env.eval(or), val(0b1110, 8));
    assert_eq!(env.eval(xor), val(0b0110, 8));
}

/// `bvnot` complements *within the width* – it does not leak the
/// infinite-precision two's complement `-value - 1`.
#[test]
fn not_stays_within_the_width() {
    let mut env = Env::new();
    let zero = env.constant(0, 8);
    let flipped = env.node(TermKind::BvNot(zero), 8);
    assert_eq!(env.eval(flipped), Some((all_ones(8), 8)));

    let narrow = env.constant(0, 4);
    let flipped_narrow = env.node(TermKind::BvNot(narrow), 4);
    assert_eq!(env.eval(flipped_narrow), Some((all_ones(4), 4)));

    let one = env.constant(1, 8);
    let flipped_one = env.node(TermKind::BvNot(one), 8);
    assert_eq!(env.eval(flipped_one), val(254, 8));
}

// ======== Shifts ========

/// A shift distance of at least the width shifts every bit out.
#[test]
fn shift_past_the_width_is_zero() {
    let mut env = Env::new();
    let value = env.constant(0xFF, 8);
    for distance in [8, 9, 255] {
        let amount = env.constant(distance, 8);
        let shl = env.node(TermKind::BvShl(value, amount), 8);
        let lshr = env.node(TermKind::BvLshr(value, amount), 8);
        assert_eq!(env.eval(shl), val(0, 8), "shl by {distance}");
        assert_eq!(env.eval(lshr), val(0, 8), "lshr by {distance}");
    }
}

/// A zero distance is the identity, and in-range distances shift within the
/// width (the left shift masking off the bits that leave the top).
#[test]
fn in_range_shifts() {
    let mut env = Env::new();
    let value = env.constant(0b1001_0110, 8);
    let zero = env.constant(0, 8);
    let identity_l = env.node(TermKind::BvShl(value, zero), 8);
    let identity_r = env.node(TermKind::BvLshr(value, zero), 8);
    assert_eq!(env.eval(identity_l), val(0b1001_0110, 8));
    assert_eq!(env.eval(identity_r), val(0b1001_0110, 8));

    let four = env.constant(4, 8);
    let left = env.node(TermKind::BvShl(value, four), 8);
    let right = env.node(TermKind::BvLshr(value, four), 8);
    assert_eq!(env.eval(left), val(0b0110_0000, 8));
    assert_eq!(env.eval(right), val(0b0000_1001, 8));

    let seven = env.constant(7, 8);
    let edge_l = env.node(TermKind::BvShl(value, seven), 8);
    let edge_r = env.node(TermKind::BvLshr(value, seven), 8);
    assert_eq!(env.eval(edge_l), val(0, 8));
    assert_eq!(env.eval(edge_r), val(1, 8));
}

/// `bvlshr` is *logical*: it zero-fills, so a top-bit-set value shifts down to
/// a small one rather than staying negative.
#[test]
fn lshr_zero_fills() {
    let mut env = Env::new();
    let value = env.constant(0b1000_0000, 8);
    let one = env.constant(1, 8);
    let shifted = env.node(TermKind::BvLshr(value, one), 8);
    assert_eq!(env.eval(shifted), val(0b0100_0000, 8));
}

/// A shift distance that does not fit in a `u64` limb is still at least the
/// width, so it shifts every bit out.
///
/// This is the case the pre-conversion evaluator got **wrong**: it read the
/// distance as `to_u64_digits().1.first().unwrap_or(0)`, i.e. only the low 64
/// bits, so `2^64` was read as a distance of `0` and `bvshl x (_ bv2^64 65)`
/// evaluated to `x` instead of `0`.  On a 65-bit sort that distance is a
/// perfectly well-sorted literal, and the wrong value feeds
/// `check_cross_theory_conflict`, which reports UNSAT when two reads of one
/// array index disagree – so the bug could manufacture a spurious `unsat`.
#[test]
fn shift_distance_past_a_u64_limb_still_clears_the_value() {
    let mut env = Env::new();
    let value = env.constant(0b1011, 65);
    let two_pow_64 = env.big_constant(BigInt::one() << 64u32, 65);
    let shl = env.node(TermKind::BvShl(value, two_pow_64), 65);
    let lshr = env.node(TermKind::BvLshr(value, two_pow_64), 65);
    assert_eq!(env.eval(shl), val(0, 65));
    assert_eq!(env.eval(lshr), val(0, 65));

    // The low limb being non-zero is not special either: 2^64 + 3 is still
    // past the width.  The old reading made this a distance of 3.
    let past = env.big_constant((BigInt::one() << 64u32) + BigInt::from(3), 65);
    let shl_past = env.node(TermKind::BvShl(value, past), 65);
    assert_eq!(env.eval(shl_past), val(0, 65));
}

/// An out-of-range literal means what it means everywhere else in the system:
/// its two's-complement reduction into `[0, 2^width)`.
///
/// `TermManager::mk_bitvec` does not normalise its argument, so a negative or
/// oversized literal is reachable through the public API.  Every leaf here goes
/// through `bv_fold::bv_wrap_unsigned` – the same reduction the term builder's
/// `bv_const_unsigned`, the SMT-LIB printer and the model builder apply – so
/// `(_ bv-1 8)` is `255` here exactly as it prints as `#xff`.
///
/// Three behaviours have now been given for this input.  The original read the
/// distance through `to_u64_digits`, which discards the sign, and shifted by the
/// *magnitude* `1`.  The iterative rewrite refused it as "not a bit-vector
/// value".  Reducing is better than either: it is one opinion instead of a third
/// one, and it is the opinion the rest of the workspace already holds.
#[test]
fn out_of_range_literals_are_reduced() {
    let mut env = Env::new();
    let negative = env.big_constant(BigInt::from(-1), 8);
    assert_eq!(env.eval(negative), val(255, 8));
    let oversized = env.big_constant(BigInt::from(256), 8);
    assert_eq!(env.eval(oversized), val(0, 8));

    // A negative *shift distance* therefore reduces to 255, which is past the
    // width, so it clears the value.  The original shifted left by one.
    let value = env.constant(0b1011, 8);
    let shl = env.node(TermKind::BvShl(value, negative), 8);
    let lshr = env.node(TermKind::BvLshr(value, negative), 8);
    assert_eq!(env.eval(shl), val(0, 8));
    assert_eq!(env.eval(lshr), val(0, 8));

    // A bound variable's recorded value is reduced the same way: it comes from
    // the same un-normalised `BitVecConst`.
    let sort = env.manager.sorts.bitvec(8);
    let var = env.manager.mk_var("neg", sort);
    env.bindings.insert(var, (BigInt::from(-2), 8));
    assert_eq!(env.eval(var), val(254, 8));
}

// ======== Signed operators, `concat` and `extract` ========

/// `bvsdiv` reads both operands as two's complement and truncates **towards
/// zero** (not floor): `-7 / 2` is `-3`, i.e. `249 / 2 = 253` at width 8.
#[test]
fn sdiv_is_signed_and_truncates_towards_zero() {
    let mut env = Env::new();
    let minus_seven = env.constant(249, 8);
    let two = env.constant(2, 8);
    let quotient = env.node(TermKind::BvSdiv(minus_seven, two), 8);
    assert_eq!(env.eval(quotient), val(253, 8));

    // Negative divisor: `7 / -2 = -3`.
    let seven = env.constant(7, 8);
    let minus_two = env.constant(254, 8);
    let mixed = env.node(TermKind::BvSdiv(seven, minus_two), 8);
    assert_eq!(env.eval(mixed), val(253, 8));

    // Both negative: `-7 / -2 = 3`.
    let both = env.node(TermKind::BvSdiv(minus_seven, minus_two), 8);
    assert_eq!(env.eval(both), val(3, 8));
}

/// `bvsdiv` is total, and the two branches at a zero divisor differ by the sign
/// of the dividend: `1` for a negative one, all-ones for a non-negative one.
#[test]
fn sdiv_by_zero_is_total_and_sign_dependent() {
    let mut env = Env::new();
    let zero = env.constant(0, 8);
    let negative = env.constant(249, 8);
    let positive = env.constant(7, 8);
    let from_negative = env.node(TermKind::BvSdiv(negative, zero), 8);
    let from_positive = env.node(TermKind::BvSdiv(positive, zero), 8);
    assert_eq!(env.eval(from_negative), val(1, 8));
    assert_eq!(env.eval(from_positive), Some((all_ones(8), 8)));
}

/// The signed extreme: `INT_MIN / -1` overflows in fixed-width two's
/// complement, and SMT-LIB's answer is the wrapped one – `-128 / -1 = 128`,
/// which is `INT_MIN` again.  Exact `BigInt` arithmetic computes `128` and the
/// reduction keeps it in range; nothing panics and nothing saturates.
#[test]
fn sdiv_at_the_signed_extreme_wraps() {
    let mut env = Env::new();
    let int_min = env.constant(0x80, 8);
    let minus_one = env.constant(0xFF, 8);
    let quotient = env.node(TermKind::BvSdiv(int_min, minus_one), 8);
    assert_eq!(env.eval(quotient), val(0x80, 8));

    let remainder = env.node(TermKind::BvSrem(int_min, minus_one), 8);
    assert_eq!(env.eval(remainder), val(0, 8));
}

/// `bvsrem` takes the sign of the **dividend**, which is what distinguishes it
/// from `bvsmod`.
#[test]
fn srem_takes_the_dividend_sign() {
    let mut env = Env::new();
    let minus_seven = env.constant(249, 8);
    let two = env.constant(2, 8);
    let seven = env.constant(7, 8);
    let minus_two = env.constant(254, 8);

    // `-7 % 2 = -1` -> 255.
    let negative_dividend = env.node(TermKind::BvSrem(minus_seven, two), 8);
    assert_eq!(env.eval(negative_dividend), val(255, 8));
    // `7 % -2 = 1` -> the dividend's sign, so positive.
    let negative_divisor = env.node(TermKind::BvSrem(seven, minus_two), 8);
    assert_eq!(env.eval(negative_divisor), val(1, 8));

    // Total at a zero divisor: the dividend.
    let zero = env.constant(0, 8);
    let by_zero = env.node(TermKind::BvSrem(minus_seven, zero), 8);
    assert_eq!(env.eval(by_zero), val(249, 8));
}

/// `bvashr` fills with copies of the **sign bit**, unlike `bvlshr`.
#[test]
fn ashr_sign_extends() {
    let mut env = Env::new();
    let negative = env.constant(0b1000_0000, 8);
    let positive = env.constant(0b0100_0000, 8);
    let one = env.constant(1, 8);
    let negative_shifted = env.node(TermKind::BvAshr(negative, one), 8);
    let positive_shifted = env.node(TermKind::BvAshr(positive, one), 8);
    assert_eq!(env.eval(negative_shifted), val(0b1100_0000, 8));
    assert_eq!(env.eval(positive_shifted), val(0b0010_0000, 8));

    // Past the width only copies of the sign bit remain.
    let eight = env.constant(8, 8);
    let negative_past = env.node(TermKind::BvAshr(negative, eight), 8);
    let positive_past = env.node(TermKind::BvAshr(positive, eight), 8);
    assert_eq!(env.eval(negative_past), Some((all_ones(8), 8)));
    assert_eq!(env.eval(positive_past), val(0, 8));
}

/// `concat` puts the left operand in the high bits and adds the widths, so it
/// is the one binary operator that requires **no** width agreement.
#[test]
fn concat_adds_the_widths() {
    let mut env = Env::new();
    let high = env.constant(0xA, 4);
    let low = env.constant(0x5, 4);
    let joined = env.node(TermKind::BvConcat(high, low), 8);
    assert_eq!(env.eval(joined), val(0xA5, 8));

    // Mismatched widths are fine and produce their sum.
    let byte = env.constant(0xFF, 8);
    let mixed = env.node(TermKind::BvConcat(high, byte), 12);
    assert_eq!(env.eval(mixed), val(0xAFF, 12));

    // Order matters.
    let reversed = env.node(TermKind::BvConcat(low, high), 8);
    assert_eq!(env.eval(reversed), val(0x5A, 8));
}

/// `(_ extract high low)` narrows to `high - low + 1` bits, right-aligned.
#[test]
fn extract_narrows_the_width() {
    let mut env = Env::new();
    let value = env.constant(0xA5, 8);
    let cases = [
        (3u32, 0u32, 0x5i64, 4u32),
        (7, 4, 0xA, 4),
        (7, 0, 0xA5, 8),
        (0, 0, 1, 1),
        (7, 7, 1, 1),
        (5, 2, 0b1001, 4),
    ];
    for (high, low, expected, width) in cases {
        let term = env.node(
            TermKind::BvExtract {
                high,
                low,
                arg: value,
            },
            width,
        );
        assert_eq!(
            env.eval(term),
            val(expected, width),
            "extract {high}..{low}"
        );
    }
}

/// An out-of-range `extract` index is not folded to a fabricated value.
///
/// This matches `TermManager::mk_bv_extract`, which leaves malformed indices
/// "for the parser's sort check rather than silently folding".  The width
/// arithmetic is checked, so `low > high` cannot underflow into a ~4-billion-bit
/// result.
#[test]
fn malformed_extract_indices_are_refused() {
    let mut env = Env::new();
    let value = env.constant(0xA5, 8);
    let malformed = [(0u32, 1u32), (3, 7), (8, 0), (8, 8), (u32::MAX, 0)];
    for (high, low) in malformed {
        let term = env.node(
            TermKind::BvExtract {
                high,
                low,
                arg: value,
            },
            8,
        );
        assert_eq!(env.eval(term), None, "extract {high}..{low}");
    }
}

/// The new kinds compose with the old ones and with each other, and the widths
/// thread through: `extract 7..4 (concat 0xA:4 0x5:4)` is `0xA:4`.
#[test]
fn new_kinds_compose() {
    let mut env = Env::new();
    let high = env.constant(0xA, 4);
    let low = env.constant(0x5, 4);
    let joined = env.node(TermKind::BvConcat(high, low), 8);
    let sliced = env.node(
        TermKind::BvExtract {
            high: 7,
            low: 4,
            arg: joined,
        },
        4,
    );
    assert_eq!(env.eval(sliced), val(0xA, 4));

    // A width-mismatched op over a `concat` result is still refused: the
    // `concat` widened to 8, so adding a 4-bit operand does not fold.
    let mismatched = env.node(TermKind::BvAdd(joined, high), 8);
    assert_eq!(env.eval(mismatched), None);

    // But adding an 8-bit operand does.
    let byte = env.constant(1, 8);
    let matched = env.node(TermKind::BvAdd(joined, byte), 8);
    assert_eq!(env.eval(matched), val(0xA6, 8));
}

// ======== Structure ========

/// A variable substituted under arithmetic – the pattern the cross-theory
/// check exists for: `x = 5` makes `bvadd(x, 1)` evaluate to `6`.
#[test]
fn variables_are_substituted_under_arithmetic() {
    let mut env = Env::new();
    let x = env.bound_var("x", 5, 8);
    let one = env.constant(1, 8);
    let sum = env.node(TermKind::BvAdd(x, one), 8);
    assert_eq!(env.eval(sum), val(6, 8));
}

/// A shared subterm is visited once per *edge*, and both visits agree.  The
/// evaluator has no memo table, and this pins that the absence of one is not
/// observable in the answer.
#[test]
fn a_shared_subterm_evaluates_the_same_under_both_parents() {
    let mut env = Env::new();
    let x = env.bound_var("x", 3, 8);
    let one = env.constant(1, 8);
    let shared = env.node(TermKind::BvAdd(x, one), 8);
    let doubled = env.node(TermKind::BvAdd(shared, shared), 8);
    let squared = env.node(TermKind::BvMul(shared, shared), 8);
    assert_eq!(env.eval(shared), val(4, 8));
    assert_eq!(env.eval(doubled), val(8, 8));
    assert_eq!(env.eval(squared), val(16, 8));
}

/// A single unevaluable leaf anywhere in the term makes the whole term
/// unevaluable – the failure is not swallowed at the arm that saw it.
#[test]
fn one_unevaluable_leaf_defeats_the_whole_term() {
    let mut env = Env::new();
    let free = env.free_var("free", 8);
    let one = env.constant(1, 8);
    let mut term = free;
    for _ in 0..8 {
        term = env.node(TermKind::BvAdd(term, one), 8);
        term = env.node(TermKind::BvNot(term), 8);
    }
    assert_eq!(env.eval(term), None);
}

/// Nesting on the right-hand operand is evaluated too – a frame that forgot
/// its second operand would silently reuse the first.
#[test]
fn right_hand_nesting_is_evaluated() {
    let mut env = Env::new();
    let two = env.constant(2, 8);
    let three = env.constant(3, 8);
    let inner = env.node(TermKind::BvMul(two, three), 8);
    let outer = env.node(TermKind::BvSub(inner, two), 8);
    assert_eq!(env.eval(inner), val(6, 8));
    assert_eq!(env.eval(outer), val(4, 8));
    // Order matters for a non-commutative op: `2 - 6` must wrap, not saturate.
    let reversed = env.node(TermKind::BvSub(two, inner), 8);
    assert_eq!(env.eval(reversed), val(252, 8));
}

// ======== `ite` and its conditions ========

/// `ite` folds only the **taken** branch.
///
/// The untaken branch here cannot be folded at all, so if the walk visited it
/// the whole term would answer *not evaluable*.  That makes the short circuit
/// observable rather than merely a cost saving.
#[test]
fn ite_evaluates_only_the_taken_branch() {
    let mut env = Env::new();
    let taken = env.constant(0x11, 8);
    let unevaluable = env.free_var("never", 8);
    let yes = env.manager.mk_true();
    let no = env.manager.mk_false();

    let then_taken = env.node(TermKind::Ite(yes, taken, unevaluable), 8);
    assert_eq!(env.eval(then_taken), val(0x11, 8));

    let else_taken = env.node(TermKind::Ite(no, unevaluable, taken), 8);
    assert_eq!(env.eval(else_taken), val(0x11, 8));
}

/// A condition that is an equality over bound bit-vector variables decides the
/// branch.  This is the shape that made `check_cross_theory_conflict` answer
/// `sat` for an unsatisfiable formula before `ite` had an arm.
#[test]
fn ite_condition_can_be_an_equality() {
    let mut env = Env::new();
    let x = env.bound_var("x", 5, 8);
    let five = env.constant(5, 8);
    let six = env.constant(6, 8);
    let seven = env.constant(7, 8);
    let condition = env.node(TermKind::Eq(x, five), 8);
    let term = env.node(TermKind::Ite(condition, six, seven), 8);
    assert_eq!(env.eval(term), val(6, 8));

    // Rebinding the variable takes the other branch.
    env.bindings.insert(x, (BigInt::from(4), 8));
    assert_eq!(env.eval(term), val(7, 8));
}

/// The unsigned and signed comparisons disagree on a top-bit-set operand, and
/// each takes its own branch: `#xff` is `255` unsigned but `-1` signed.
#[test]
fn unsigned_and_signed_conditions_differ() {
    let mut env = Env::new();
    let x = env.bound_var("x", 0xFF, 8);
    let one = env.constant(1, 8);
    let then_value = env.constant(0xAA, 8);
    let else_value = env.constant(0xBB, 8);

    let unsigned = env.node(TermKind::BvUlt(x, one), 8);
    let unsigned_ite = env.node(TermKind::Ite(unsigned, then_value, else_value), 8);
    // 255 < 1 is false.
    assert_eq!(env.eval(unsigned_ite), val(0xBB, 8));

    let signed = env.node(TermKind::BvSlt(x, one), 8);
    let signed_ite = env.node(TermKind::Ite(signed, then_value, else_value), 8);
    // -1 < 1 is true.
    assert_eq!(env.eval(signed_ite), val(0xAA, 8));
}

/// The reflexive comparisons hold at equality and the strict ones do not.
#[test]
fn comparison_conditions_at_the_boundary() {
    let mut env = Env::new();
    let x = env.bound_var("x", 0x80, 8);
    let same = env.constant(0x80, 8);
    let then_value = env.constant(1, 8);
    let else_value = env.constant(0, 8);
    let cases = [
        (TermKind::BvUlt(x, same), 0),
        (TermKind::BvUle(x, same), 1),
        (TermKind::BvSlt(x, same), 0),
        (TermKind::BvSle(x, same), 1),
        (TermKind::Eq(x, same), 1),
    ];
    for (condition, expected) in cases {
        let condition = env.node(condition, 8);
        let term = env.node(TermKind::Ite(condition, then_value, else_value), 8);
        assert_eq!(env.eval(term), val(expected, 8), "condition {condition:?}");
    }
}

/// `not` composes over a condition.
#[test]
fn ite_condition_can_be_negated() {
    let mut env = Env::new();
    let x = env.bound_var("x", 5, 8);
    let five = env.constant(5, 8);
    let then_value = env.constant(1, 8);
    let else_value = env.constant(0, 8);
    let equality = env.node(TermKind::Eq(x, five), 8);
    let negated = env.node(TermKind::Not(equality), 8);
    let term = env.node(TermKind::Ite(negated, then_value, else_value), 8);
    assert_eq!(env.eval(term), val(0, 8));
}

/// `and` and `or` short-circuit on the first decisive operand, so an operand
/// that cannot be folded at all is never reached once the answer is settled.
#[test]
fn connective_conditions_short_circuit() {
    let mut env = Env::new();
    let then_value = env.constant(1, 8);
    let else_value = env.constant(0, 8);
    let yes = env.manager.mk_true();
    let no = env.manager.mk_false();
    // A condition with no arm at all: an unbound Boolean variable.
    let bool_sort = env.manager.sorts.bool_sort;
    let undecidable = env.manager.mk_var("p", bool_sort);

    // `(and false p)` is false without ever opening `p`.
    let conjunction = env.node(TermKind::And(smallvec![no, undecidable]), 8);
    let short_false = env.node(TermKind::Ite(conjunction, then_value, else_value), 8);
    assert_eq!(env.eval(short_false), val(0, 8));

    // `(or true p)` is true without ever opening `p`.
    let disjunction = env.node(TermKind::Or(smallvec![yes, undecidable]), 8);
    let short_true = env.node(TermKind::Ite(disjunction, then_value, else_value), 8);
    assert_eq!(env.eval(short_true), val(1, 8));

    // With the undecidable operand first there is nothing to short-circuit on,
    // and the whole term does not fold.  That is the conservative direction.
    let blocked = env.node(TermKind::And(smallvec![undecidable, no]), 8);
    let blocked_ite = env.node(TermKind::Ite(blocked, then_value, else_value), 8);
    assert_eq!(env.eval(blocked_ite), None);
}

/// Every operand of a connective is consulted when none is decisive, and the
/// empty connective is its identity.
#[test]
fn connective_conditions_fold_every_operand() {
    let mut env = Env::new();
    let then_value = env.constant(1, 8);
    let else_value = env.constant(0, 8);
    let yes = env.manager.mk_true();
    let no = env.manager.mk_false();

    let all_true = env.node(TermKind::And(smallvec![yes, yes, yes]), 8);
    let term = env.node(TermKind::Ite(all_true, then_value, else_value), 8);
    assert_eq!(env.eval(term), val(1, 8));

    // A `false` in the trailing position still decides it.
    let trailing = env.node(TermKind::And(smallvec![yes, yes, no]), 8);
    let trailing_ite = env.node(TermKind::Ite(trailing, then_value, else_value), 8);
    assert_eq!(env.eval(trailing_ite), val(0, 8));

    let empty_and = env.node(TermKind::And(smallvec![]), 8);
    let empty_and_ite = env.node(TermKind::Ite(empty_and, then_value, else_value), 8);
    assert_eq!(env.eval(empty_and_ite), val(1, 8));

    let empty_or = env.node(TermKind::Or(smallvec![]), 8);
    let empty_or_ite = env.node(TermKind::Ite(empty_or, then_value, else_value), 8);
    assert_eq!(env.eval(empty_or_ite), val(0, 8));
}

/// A condition this evaluator cannot decide leaves the whole term unfolded, and
/// so does an `ite` whose branches are not bit-vector-sorted.
#[test]
fn undecidable_ite_does_not_fold() {
    let mut env = Env::new();
    let then_value = env.constant(1, 8);
    let else_value = env.constant(0, 8);

    // An unbound Boolean variable.
    let bool_sort = env.manager.sorts.bool_sort;
    let undecidable = env.manager.mk_var("p", bool_sort);
    let unbound = env.node(TermKind::Ite(undecidable, then_value, else_value), 8);
    assert_eq!(env.eval(unbound), None);

    // A comparison whose operand widths disagree.
    let wide = env.constant(3, 8);
    let narrow = env.constant(3, 4);
    let mismatched = env.node(TermKind::BvUlt(wide, narrow), 8);
    let mismatched_ite = env.node(TermKind::Ite(mismatched, then_value, else_value), 8);
    assert_eq!(env.eval(mismatched_ite), None);

    // An equality between two Boolean operands is not a bit-vector comparison.
    let boolean_eq = env.node(TermKind::Eq(undecidable, undecidable), 8);
    let boolean_ite = env.node(TermKind::Ite(boolean_eq, then_value, else_value), 8);
    assert_eq!(env.eval(boolean_ite), None);

    // Integer branches do not fold as bit-vectors.
    let int = env.manager.mk_int(1);
    let yes = env.manager.mk_true();
    let int_ite = env.node(TermKind::Ite(yes, int, int), 8);
    assert_eq!(env.eval(int_ite), None);
}

/// `ite` composes with the arithmetic around it.
#[test]
fn ite_composes_under_arithmetic() {
    let mut env = Env::new();
    let x = env.bound_var("x", 5, 8);
    let five = env.constant(5, 8);
    let one = env.constant(1, 8);
    let two = env.constant(2, 8);
    let condition = env.node(TermKind::Eq(x, five), 8);
    let chosen = env.node(TermKind::Ite(condition, one, two), 8);
    let sum = env.node(TermKind::BvAdd(x, chosen), 8);
    assert_eq!(env.eval(sum), val(6, 8));
}

// ======== Corpus equivalence ========

/// A deterministic 64-bit xorshift, so the corpus below is reproducible
/// without a random-number dependency.
struct Xorshift(u64);

impl Xorshift {
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    /// A value in `0..bound`; `bound` is never zero at any call site.
    fn below(&mut self, bound: usize) -> usize {
        (self.next_u64() % bound as u64) as usize
    }
}

/// The `TermKind` shapes the *legacy* corpus draws from: exactly the thirteen
/// the pre-delegation evaluator implemented.
///
/// Frozen at twelve draw slots so the legacy corpus stays byte-identical to the
/// one the pre-delegation implementation was compared against; the extended
/// shapes take slots after it, and [`draw_operator`]'s slots `0..12` are
/// untouched.
const LEGACY_CORPUS_OPS: usize = 12;

/// The shapes that preserve the left operand's width, so a per-width pool stays
/// width-homogeneous: the legacy twelve plus `bvashr`, `bvsdiv`, `bvsrem` and
/// `ite`.
const WIDTH_PRESERVING_CORPUS_OPS: usize = 16;

/// Every shape [`draw_operator`] can draw, adding the two that change the width:
/// `concat` and `extract`.
const EXTENDED_CORPUS_OPS: usize = 18;

/// The largest expanded (tree, not DAG) node count a corpus term may have.
/// The evaluator has no memo table, so a term's cost is its *tree* size; the
/// cap keeps the corpus quadratic rather than exponential.
const CORPUS_TREE_CAP: u64 = 48;

/// One growing pool of terms, with each term's expanded tree size alongside.
struct Pool {
    terms: Vec<TermId>,
    sizes: Vec<u64>,
}

impl Pool {
    fn new() -> Self {
        Self {
            terms: Vec::new(),
            sizes: Vec::new(),
        }
    }

    fn push(&mut self, term: TermId, size: u64) {
        self.terms.push(term);
        self.sizes.push(size);
    }
}

/// Draw two operands and build one operator node over them, returning it with
/// its expanded tree size.  `None` when the draw would exceed the tree cap.
///
/// `op_count` selects how many shapes are in play – [`LEGACY_CORPUS_OPS`] for
/// the corpus the pre-delegation implementation was compared against, or
/// [`EXTENDED_CORPUS_OPS`] to include the newly covered kinds.  Slots `0..12`
/// draw no extra randomness, so passing the legacy count reproduces the legacy
/// corpus draw for draw, node for node.
fn draw_operator(
    env: &mut Env,
    rng: &mut Xorshift,
    left: (TermId, u64),
    right: (TermId, u64),
    op_count: usize,
) -> Option<(TermId, u64)> {
    let (lhs, left_size) = left;
    let (rhs, right_size) = right;
    let binary_size = left_size + right_size + 1;
    if binary_size > CORPUS_TREE_CAP {
        return None;
    }
    let left_width = env.width_of(lhs);
    let right_width = env.width_of(rhs);
    let (kind, tree_size, width) = match rng.below(op_count) {
        0 => (TermKind::BvAdd(lhs, rhs), binary_size, left_width),
        1 => (TermKind::BvSub(lhs, rhs), binary_size, left_width),
        2 => (TermKind::BvMul(lhs, rhs), binary_size, left_width),
        3 => (TermKind::BvUdiv(lhs, rhs), binary_size, left_width),
        4 => (TermKind::BvUrem(lhs, rhs), binary_size, left_width),
        5 => (TermKind::BvAnd(lhs, rhs), binary_size, left_width),
        6 => (TermKind::BvOr(lhs, rhs), binary_size, left_width),
        7 => (TermKind::BvXor(lhs, rhs), binary_size, left_width),
        8 => (TermKind::BvShl(lhs, rhs), binary_size, left_width),
        9 => (TermKind::BvLshr(lhs, rhs), binary_size, left_width),
        10 => (TermKind::BvNot(lhs), left_size + 1, left_width),
        // The node's declared width is the *left* operand's here, which is not
        // this node's own width.  It is preserved exactly because the interned
        // sort is part of a term's identity, and changing it would renumber the
        // legacy corpus and void its comparison against the pre-delegation
        // implementation.  The evaluator never reads a node's declared sort.
        11 => (TermKind::BvNot(rhs), right_size + 1, left_width),
        // Slots 12..16 exist only in the extended corpus and all preserve the
        // left operand's width, so a width-homogeneous pool stays homogeneous.
        12 => (TermKind::BvAshr(lhs, rhs), binary_size, left_width),
        13 => (TermKind::BvSdiv(lhs, rhs), binary_size, left_width),
        14 => (TermKind::BvSrem(lhs, rhs), binary_size, left_width),
        // An `ite` over a comparison of the two operands, so the condition is
        // decidable exactly when both operands are.
        15 => {
            let condition = match rng.below(5) {
                0 => TermKind::Eq(lhs, rhs),
                1 => TermKind::BvUlt(lhs, rhs),
                2 => TermKind::BvUle(lhs, rhs),
                3 => TermKind::BvSlt(lhs, rhs),
                _ => TermKind::BvSle(lhs, rhs),
            };
            let condition = env.node(condition, left_width);
            (
                TermKind::Ite(condition, lhs, rhs),
                binary_size + 1,
                left_width,
            )
        }
        // The last two slots *change* the width, so they are drawn only in the
        // cross-width layer; inside a per-width pool they would turn almost
        // every later draw into a width mismatch and starve the value coverage.
        16 => (
            TermKind::BvConcat(lhs, rhs),
            binary_size,
            left_width.saturating_add(right_width),
        ),
        _ => {
            // An in-range slice of the left operand: `high` below its width and
            // `low` no higher than `high`.
            let high = rng.below(left_width.max(1) as usize) as u32;
            let low = rng.below(high as usize + 1) as u32;
            (
                TermKind::BvExtract {
                    high,
                    low,
                    arg: lhs,
                },
                left_size + 1,
                high - low + 1,
            )
        }
    };
    Some((env.node(kind, width), tree_size))
}

/// The boundary literals of a width: zero, one, both sides of the sign bit,
/// and both ends of the range.
fn boundary_values(width: u32) -> [BigInt; 6] {
    let top = all_ones(width);
    let half = top.clone() >> 1u32;
    [
        BigInt::zero(),
        BigInt::one(),
        half.clone(),
        half + BigInt::one(),
        top.clone() - BigInt::one(),
        top,
    ]
}

/// Build a corpus of bit-vector terms in two layers.
///
/// The first layer is one pool per width whose operands always agree in width,
/// so the arithmetic, bitwise and shift arms are exercised on terms that
/// actually evaluate – including the wrap-around and total-division cases,
/// since every pool starts from that width's boundary literals.
///
/// The second layer draws operands across widths and mixes in a free variable
/// and three kinds the evaluator does not implement, so the width-mismatch
/// rejections and the "not evaluable" propagation are exercised as well.
///
/// Terms are interned raw throughout, so the builder's constant folding never
/// pre-computes an answer the evaluator was supposed to produce.
fn build_corpus(
    per_width: usize,
    mixed: usize,
    clean_ops: usize,
    mixed_ops: usize,
) -> (Env, Vec<TermId>) {
    let mut env = Env::new();
    let mut rng = Xorshift(0x9E37_79B9_7F4A_7C15);
    let mut seen: FxHashSet<TermId> = FxHashSet::default();
    let mut corpus: Vec<TermId> = Vec::new();
    let mut clean = Pool::new();

    for (index, &width) in [4u32, 8, 16].iter().enumerate() {
        let mut pool = Pool::new();
        for value in boundary_values(width) {
            let term = env.big_constant(value, width);
            pool.push(term, 1);
        }
        let bound = env.bound_var(&format!("x{index}"), 3 * index as i64 + 1, width);
        pool.push(bound, 1);

        let mut attempts = 0usize;
        while pool.terms.len() < per_width && attempts < per_width * 64 {
            attempts += 1;
            let left = rng.below(pool.terms.len());
            let right = rng.below(pool.terms.len());
            let Some((term, size)) = draw_operator(
                &mut env,
                &mut rng,
                (pool.terms[left], pool.sizes[left]),
                (pool.terms[right], pool.sizes[right]),
                clean_ops,
            ) else {
                continue;
            };
            if !seen.insert(term) {
                // Hash consing gave back an existing node; keep drawing.
                continue;
            }
            pool.push(term, size);
        }
        assert_eq!(pool.terms.len(), per_width, "clean pool for width {width}");
        corpus.extend(pool.terms.iter().copied());
        for (term, size) in pool.terms.into_iter().zip(pool.sizes) {
            clean.push(term, size);
        }
    }

    // Poison leaves: an unbound variable and three kinds with no arm.
    let free = env.free_var("free", 8);
    clean.push(free, 1);
    corpus.push(free);
    let a = clean.terms[0];
    let b = clean.terms[1];
    for kind in [
        TermKind::BvAshr(a, b),
        TermKind::BvSdiv(a, b),
        TermKind::BvConcat(a, b),
    ] {
        let term = env.node(kind, 8);
        clean.push(term, 1);
        corpus.push(term);
    }
    let int = env.manager.mk_int(3);
    clean.push(int, 1);
    corpus.push(int);

    let mut produced = 0usize;
    let mut attempts = 0usize;
    while produced < mixed && attempts < mixed * 64 {
        attempts += 1;
        let left = rng.below(clean.terms.len());
        let right = rng.below(clean.terms.len());
        let Some((term, size)) = draw_operator(
            &mut env,
            &mut rng,
            (clean.terms[left], clean.sizes[left]),
            (clean.terms[right], clean.sizes[right]),
            mixed_ops,
        ) else {
            continue;
        };
        if !seen.insert(term) {
            continue;
        }
        clean.push(term, size);
        corpus.push(term);
        produced += 1;
    }
    assert_eq!(produced, mixed, "mixed pool");

    (env, corpus)
}

/// FNV-1a over the rendered evaluation of every corpus term, in corpus order.
fn corpus_digest(env: &Env, terms: &[TermId]) -> (u64, usize) {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    let mut evaluable = 0usize;
    for (index, &term) in terms.iter().enumerate() {
        let rendered = env.rendered(term);
        if rendered != "-" {
            evaluable += 1;
        }
        for byte in format!("{index}:{rendered};").bytes() {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    (hash, evaluable)
}

/// The legacy corpus digest, pinned.
///
/// This corpus draws only from the thirteen kinds the **pre-delegation
/// recursive** implementation of `evaluate_bv_expr` supported, and is generated
/// draw for draw identically to the one that implementation was measured
/// against.  Every one of its 4105 answers was compared term by term against a
/// verbatim copy of that implementation:
///
/// * **4099 identical** – same value at the same width, or `None` in both.
/// * **6 answered where it did not**, all reached through the three poison
///   leaves the corpus plants (`bvashr`, `bvsdiv`, `concat` over two width-4
///   literals) plus three terms built over them: `bvashr(0,1) = 0`,
///   `bvsdiv(0,1) = 0`, `concat(0,1) = 1@8`, `bvudiv(x, 0) = all-ones`,
///   `bvnot(0) = 15@4`, `bvand(0, x) = 0`.
/// * **0 regressions** – no term it could answer is answered differently now.
///
/// So `PINNED_EVALUABLE` is 3878 + 6, and the digest below differs from the
/// recursive one (`10912996395759728779`) in exactly those six positions.  Any
/// further movement means a width picked from the wrong operand, a mask applied
/// one place too early, or a dropped operand.
#[test]
fn legacy_corpus_matches_the_pinned_digest() {
    let (env, terms) = build_corpus(1200, 500, LEGACY_CORPUS_OPS, LEGACY_CORPUS_OPS);
    let (digest, evaluable) = corpus_digest(&env, &terms);
    assert_eq!(terms.len(), 4105, "corpus size");
    assert_eq!(evaluable, LEGACY_PINNED_EVALUABLE, "evaluable corpus terms");
    assert_eq!(digest, LEGACY_PINNED_DIGEST, "corpus digest");
}

/// Corpus terms that fold: the recursive implementation managed 3878, and the
/// six listed on [`legacy_corpus_matches_the_pinned_digest`] were added by
/// delegating to `bv_fold`.
const LEGACY_PINNED_EVALUABLE: usize = 3878 + 6;
/// FNV-1a digest over the legacy corpus.
const LEGACY_PINNED_DIGEST: u64 = 1_998_543_053_400_706_908;

/// The extended corpus digest, pinned.
///
/// Same generator, but drawing from every shape as well: `bvashr`, `bvsdiv`,
/// `bvsrem`, `concat`, in-range `extract`, and `ite` over each of the five
/// comparisons.  Nothing pins these answers to a previous implementation –
/// there was none – so the value tests above are what establish them and this
/// digest is what keeps them from drifting.
#[test]
fn extended_corpus_matches_the_pinned_digest() {
    let (env, terms) = build_corpus(1200, 500, WIDTH_PRESERVING_CORPUS_OPS, EXTENDED_CORPUS_OPS);
    let (digest, evaluable) = corpus_digest(&env, &terms);
    assert_eq!(terms.len(), 4105, "corpus size");
    assert_eq!(
        evaluable, EXTENDED_PINNED_EVALUABLE,
        "evaluable corpus terms"
    );
    assert_eq!(digest, EXTENDED_PINNED_DIGEST, "corpus digest");
}

/// Corpus terms that fold in the extended corpus.
const EXTENDED_PINNED_EVALUABLE: usize = 3901;
/// FNV-1a digest over the extended corpus.
const EXTENDED_PINNED_DIGEST: u64 = 9_613_999_152_448_810_278;

// ======== Native stack usage ========

/// A left-nested chain of `depth` `bvnot`s over a bound variable, plus its
/// expected value (`bvnot` is an involution, so an even chain is the identity).
fn not_chain(env: &mut Env, depth: usize) -> (TermId, BigInt) {
    let base = env.bound_var("deep", 0b0101, 8);
    let mut term = base;
    for _ in 0..depth {
        term = env.node(TermKind::BvNot(term), 8);
    }
    let expected = if depth.is_multiple_of(2) {
        BigInt::from(0b0101)
    } else {
        BigInt::from(0b1111_1010)
    };
    (term, expected)
}

/// The evaluator's native stack usage is constant in the term's depth.
///
/// A 25 000-deep chain is evaluated on a **128 KiB** thread – one eighth of
/// the 1 MiB embedders commonly give a worker, paired with one eighth of the
/// historical 200 000 levels so the ~5 bytes of stack per level this pins is
/// unchanged at a 64th of the construction cost.  The recursive
/// implementation this replaced aborted the *process* at roughly 840 levels
/// on a stack this size (6 700 on 1 MiB), so the assertion that matters here
/// is that the thread returned at all; a stack overflow is not a catchable
/// failure.
#[test]
fn deep_terms_evaluate_on_a_small_stack() {
    // Stack and depth scale together (1 MiB/200k -> 128 KiB/25k): the
    // ~5 B-per-frame threshold is the pin, so never raise one alone.
    const DEPTH: usize = 25_000;

    let observed = std::thread::Builder::new()
        .stack_size(1 << 17)
        .spawn(|| {
            let mut env = Env::new();
            let (term, expected) = not_chain(&mut env, DEPTH);
            (env.eval(term), expected)
        })
        .expect("spawn worker thread")
        .join()
        .expect("worker thread must return, not abort");

    assert_eq!(observed.0, Some((observed.1, 8)));
}

/// The same chain, but with an unevaluable leaf: the abort path unwinds the
/// heap frame stack without recursing either.
#[test]
fn deep_unevaluable_terms_also_stay_off_the_native_stack() {
    // Stack and depth scale together (1 MiB/200k -> 128 KiB/25k): the
    // ~5 B-per-frame threshold is the pin, so never raise one alone.
    const DEPTH: usize = 25_000;

    let observed = std::thread::Builder::new()
        .stack_size(1 << 17)
        .spawn(|| {
            let mut env = Env::new();
            let free = env.free_var("free", 8);
            let mut term = free;
            for _ in 0..DEPTH {
                term = env.node(TermKind::BvNot(term), 8);
            }
            env.eval(term)
        })
        .expect("spawn worker thread")
        .join()
        .expect("worker thread must return, not abort");

    assert_eq!(observed, None);
}

/// A right-leaning chain exercises the frame's *second* operand slot at depth:
/// `bvsub(1, bvsub(1, ...))` keeps a finished left value in every frame.
#[test]
fn deep_right_leaning_terms_evaluate_on_a_small_stack() {
    // Stack and depth scale together (1 MiB/100k -> 128 KiB/12.5k): the
    // ~10 B-per-frame threshold is the pin, so never raise one alone.
    const DEPTH: usize = 12_500;

    let observed = std::thread::Builder::new()
        .stack_size(1 << 17)
        .spawn(|| {
            let mut env = Env::new();
            let one = env.constant(1, 8);
            let mut term = env.constant(0, 8);
            for _ in 0..DEPTH {
                term = env.node(TermKind::BvSub(one, term), 8);
            }
            env.eval(term)
        })
        .expect("spawn worker thread")
        .join()
        .expect("worker thread must return, not abort");

    // `1 - (1 - (… - 0))` alternates between 0 and 1; an even chain is 0.
    assert_eq!(observed, val(0, 8));
}
