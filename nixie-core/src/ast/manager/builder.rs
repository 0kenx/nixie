//! Term builder methods for TermManager – all mk_* constructors

use super::super::term::{RoundingMode, TermId, TermKind};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::sort::SortId;
use num_bigint::BigInt;
use num_rational::{BigRational, Rational64};
use num_traits::{Euclid, One, ToPrimitive, Zero};
// ---------------------------------------------------------------------------
// Constant folding at construction time (Z3's `arith_rewriter` policy).
//
// Ground arithmetic is decided the moment the term is built, exactly and in
// `BigInt` / `BigRational` – never through the `Rational64` the linear
// tableau carries, whose fixed width used to overflow (a release build
// *silently wraps* there, which is a soundness hazard, not just the
// `panic = "abort"` the dev build shows) on sums like
// `9223372036854775807 + 1`, and which cannot represent the wide literals
// at all.  Folding here fixes every downstream consumer at once: the linear
// parse, the axiom instantiation, the model printer.
//
// Rules of engagement, each one load-bearing:
//
// * **Exactness over convenience** – integer sums/products/quotients fold in
//   `BigInt`; real sums/products fold in `BigRational` and are only kept
//   when the result is representable as the `Rational64` a `RealConst`
//   stores (otherwise the operands are left in place – sound, merely less
//   folded).
// * **Sort preservation** – a folded constant carries the *node's* sort: a
//   zero produced inside a `Real`-sorted product is `0.0`, not `0`.  A
//   folded integer sub-sum inside a `Real` node stays an `IntConst`
//   argument (integer addition commutes with the coercion, so this is
//   exact).
// * **Division by zero never folds** – SMT-LIB treats `(div m 0)` /
//   `(mod m 0)` as uninterpreted; the solver's `arith_axioms` relies on
//   the term surviving to carry that meaning.  Folding it to anything
//   would fabricate a value SMT-LIB does not define.
// * **Euclidean semantics** – `div`/`mod` fold with `div_euclid`/
//   `rem_euclid`, the exact semantics the theory's defining axioms assert
//   (`m = n·q + r ∧ 0 ≤ r < |n|`), so the folder and the axiomatiser can
//   never disagree about a value.
// ---------------------------------------------------------------------------

/// The SMT-LIB sort of an arithmetic node over `operands`: `Int` unless an
/// operand is `Real`-sorted (`Int` is a subsort of `Real`, so one Real
/// operand makes the node Real).  This is the standard's mixed-arithmetic
/// rule and the fix for a whole mislabeling class: `mk_add` used to take the
/// sort from `args[0]`, so `(+ xi yr)` was `Int`-sorted while `(+ yr xi)`
/// was `Real`-sorted — the same value, two labels, and the `Int` label
/// feeds integer-only reasoning (`assert_eq`'s GCD test, strict-inequality
/// tightening) a row whose value can be fractional.
fn unified_arith_sort<'a>(
    fallback: TermId,
    operands: impl IntoIterator<Item = &'a TermId>,
    manager: &TermManager,
) -> SortId {
    let mut sort = manager
        .get(fallback)
        .map_or(manager.sorts.int_sort, |t| t.sort);
    let real_sort = manager.sorts.real_sort;
    for &t in operands {
        if manager.get(t).is_some_and(|n| n.sort == real_sort) {
            sort = real_sort;
        }
    }
    sort
}

/// View a term as an integer constant (for folding), by value.
#[must_use]
fn int_const_of(t: TermId, manager: &TermManager) -> Option<BigInt> {
    match &manager.get(t)?.kind {
        TermKind::IntConst(v) => Some(v.clone()),
        _ => None,
    }
}

/// View a term as a rational constant (for folding), widened to `BigRational`.
#[must_use]
fn real_const_of(t: TermId, manager: &TermManager) -> Option<BigRational> {
    match &manager.get(t)?.kind {
        TermKind::RealConst(r) => Some(BigRational::new(
            BigInt::from(*r.numer()),
            BigInt::from(*r.denom()),
        )),
        _ => None,
    }
}

/// Fold a comparison of two numeric constants (Int/Real mixtures compare
/// as exact rationals — `Int` is a subsort of `Real`), returning the
/// truth value when both sides are numerals.  Z3's `arith_rewriter` folds
/// numeral comparisons; without this, `3.5 > 3` survived as an atom only
/// the tableau could close.
fn numeric_cmp_fold(
    lhs: TermId,
    rhs: TermId,
    manager: &TermManager,
) -> Option<core::cmp::Ordering> {
    let as_big = |t: TermId| -> Option<BigRational> {
        match &manager.get(t)?.kind {
            TermKind::IntConst(n) => Some(BigRational::from(n.clone())),
            TermKind::RealConst(r) => Some(BigRational::new(
                BigInt::from(*r.numer()),
                BigInt::from(*r.denom()),
            )),
            _ => None,
        }
    };
    let (a, b) = (as_big(lhs)?, as_big(rhs)?);
    Some(a.cmp(&b))
}

/// Narrow a `BigRational` back to the `Rational64` a `RealConst` stores.
/// `None` means the exact value is not representable and the caller must not
/// fold (keeping the original operands is always sound).
#[must_use]
fn narrow_rational(r: BigRational) -> Option<Rational64> {
    let (n, d) = r.into();
    Some(Rational64::new(n.to_i64()?, d.to_i64()?))
}

use smallvec::SmallVec;

use super::TermManager;
use super::bv_fold;
use super::str_fold;

/// Canonicalize operand order for commutative binary operators so that
/// `op(a, b)` and `op(b, a)` hash-cons to the same term.
fn canonical_pair(lhs: TermId, rhs: TermId) -> (TermId, TermId) {
    if lhs.0 <= rhs.0 {
        (lhs, rhs)
    } else {
        (rhs, lhs)
    }
}

impl TermManager {
    /// Create the boolean true constant
    #[must_use]
    pub fn mk_true(&self) -> TermId {
        self.true_id
    }

    /// Create the boolean false constant
    #[must_use]
    pub fn mk_false(&self) -> TermId {
        self.false_id
    }

    /// Create a boolean constant
    #[must_use]
    pub fn mk_bool(&self, value: bool) -> TermId {
        if value { self.true_id } else { self.false_id }
    }

    /// Create an integer constant
    pub fn mk_int(&mut self, value: impl Into<BigInt>) -> TermId {
        let sort = self.sorts.int_sort;
        self.intern(TermKind::IntConst(value.into()), sort)
    }

    /// Create a rational constant
    pub fn mk_real(&mut self, value: Rational64) -> TermId {
        let sort = self.sorts.real_sort;
        self.intern(TermKind::RealConst(value), sort)
    }

    /// Create a bit vector constant
    pub fn mk_bitvec(&mut self, value: impl Into<BigInt>, width: u32) -> TermId {
        let mut value = value.into();
        // Canonical residue: a width-`w` bit-vector denotes a value in
        // `[0, 2^w)`.  SMT-LIB's `(_ bvN W)` reads `N` modulo `2^W` (z3
        // parity: `(= (_ bv4 1) (_ bv0 1))` is VALID), and hash-consing
        // must never see two terms for one value — an out-of-range literal
        // that stays raw makes `(_ bv4 1)` and `(_ bv0 1)` distinct terms,
        // and every value-comparing fold then folds `(= 4 0)` to `false`:
        // a false `sat` on `(not (= (_ bv4 1) (_ bv0 1)))`.  Negative
        // inputs reduce to their two's-complement residue, so no
        // `BitVecConst` ever carries a negative value (the blaster's
        // `to_biguint` rejection of negative constants becomes dead).
        //
        // Fast path: in-range non-negative values (the overwhelming
        // majority) skip the modulus arithmetic entirely.
        if value.sign() == num_bigint::Sign::Minus || value.bits() > u64::from(width) {
            let modulus = BigInt::from(2u8).pow(width);
            value = ((value % &modulus) + &modulus) % &modulus;
        }
        let sort = self.sorts.bitvec(width);
        self.intern(TermKind::BitVecConst { value, width }, sort)
    }

    /// Create a named variable
    pub fn mk_var(&mut self, name: &str, sort: SortId) -> TermId {
        let spur = self.intern_str(name);
        self.intern(TermKind::Var(spur), sort)
    }

    /// Create a logical NOT
    pub fn mk_not(&mut self, arg: TermId) -> TermId {
        // Simplify double negation
        if let Some(term) = self.get(arg) {
            if let TermKind::Not(inner) = term.kind {
                return inner;
            }
            if let TermKind::True = term.kind {
                return self.false_id;
            }
            if let TermKind::False = term.kind {
                return self.true_id;
            }
        }

        let sort = self.sorts.bool_sort;
        self.intern(TermKind::Not(arg), sort)
    }

    /// Create a logical AND
    pub fn mk_and(&mut self, args: impl IntoIterator<Item = TermId>) -> TermId {
        let mut flat_args: SmallVec<[TermId; 4]> = SmallVec::new();

        for arg in args {
            if let Some(term) = self.get(arg) {
                match &term.kind {
                    TermKind::False => return self.false_id,
                    TermKind::True => continue,
                    TermKind::And(inner) => flat_args.extend(inner.iter().copied()),
                    _ => flat_args.push(arg),
                }
            } else {
                flat_args.push(arg);
            }
        }

        match flat_args.len() {
            0 => self.true_id,
            1 => flat_args[0],
            _ => {
                let sort = self.sorts.bool_sort;
                self.intern(TermKind::And(flat_args), sort)
            }
        }
    }

    /// Create a logical OR
    pub fn mk_or(&mut self, args: impl IntoIterator<Item = TermId>) -> TermId {
        let mut flat_args: SmallVec<[TermId; 4]> = SmallVec::new();

        for arg in args {
            if let Some(term) = self.get(arg) {
                match &term.kind {
                    TermKind::True => return self.true_id,
                    TermKind::False => continue,
                    TermKind::Or(inner) => flat_args.extend(inner.iter().copied()),
                    _ => flat_args.push(arg),
                }
            } else {
                flat_args.push(arg);
            }
        }

        match flat_args.len() {
            0 => self.false_id,
            1 => flat_args[0],
            _ => {
                let sort = self.sorts.bool_sort;
                self.intern(TermKind::Or(flat_args), sort)
            }
        }
    }

    /// Create a logical implication
    pub fn mk_implies(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Simplifications
        if let Some(term) = self.get(lhs) {
            if let TermKind::False = term.kind {
                return self.true_id;
            }
            if let TermKind::True = term.kind {
                return rhs;
            }
        }
        if let Some(term) = self.get(rhs)
            && let TermKind::True = term.kind
        {
            return self.true_id;
        }

        let sort = self.sorts.bool_sort;
        self.intern(TermKind::Implies(lhs, rhs), sort)
    }

    /// Create a logical XOR
    pub fn mk_xor(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Simplifications
        if lhs == rhs {
            return self.false_id;
        }
        if let Some(term) = self.get(lhs) {
            if let TermKind::False = term.kind {
                return rhs;
            }
            if let TermKind::True = term.kind {
                return self.mk_not(rhs);
            }
        }
        if let Some(term) = self.get(rhs) {
            if let TermKind::False = term.kind {
                return lhs;
            }
            if let TermKind::True = term.kind {
                return self.mk_not(lhs);
            }
        }

        let sort = self.sorts.bool_sort;
        self.intern(TermKind::Xor(lhs, rhs), sort)
    }

    /// Create an if-then-else
    pub fn mk_ite(&mut self, cond: TermId, then_branch: TermId, else_branch: TermId) -> TermId {
        // Simplifications
        if let Some(term) = self.get(cond) {
            if let TermKind::True = term.kind {
                return then_branch;
            }
            if let TermKind::False = term.kind {
                return else_branch;
            }
        }
        if then_branch == else_branch {
            return then_branch;
        }
        // ite(c, true, false) => c
        let then_is_true = self
            .get(then_branch)
            .is_some_and(|t| matches!(t.kind, TermKind::True));
        let else_is_false = self
            .get(else_branch)
            .is_some_and(|t| matches!(t.kind, TermKind::False));
        if then_is_true && else_is_false {
            return cond;
        }

        let sort = self
            .get(then_branch)
            .map_or(self.sorts.bool_sort, |t| t.sort);
        self.intern(TermKind::Ite(cond, then_branch, else_branch), sort)
    }

    /// Create an equality
    pub fn mk_eq(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if lhs == rhs {
            return self.true_id;
        }

        // Check for constant comparisons
        let lhs_kind = self.get(lhs).map(|t| t.kind.clone());
        let rhs_kind = self.get(rhs).map(|t| t.kind.clone());

        match (&lhs_kind, &rhs_kind) {
            // Integer constants
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => {
                return self.mk_bool(a == b);
            }
            // Mixed numeric constants (`Int` and `Real` are comparable:
            // `Int` is a subsort of `Real`): compare as exact rationals.
            // Without this, `3.5 = 3` survived as a structural `Eq` node
            // and could be answered `sat`.
            (Some(TermKind::IntConst(_)), Some(TermKind::RealConst(_)))
            | (Some(TermKind::RealConst(_)), Some(TermKind::IntConst(_)))
            | (Some(TermKind::RealConst(_)), Some(TermKind::RealConst(_))) => {
                let as_big = |k: &Option<TermKind>| -> Option<BigRational> {
                    match k {
                        Some(TermKind::IntConst(n)) => Some(BigRational::from(n.clone())),
                        Some(TermKind::RealConst(r)) => Some(BigRational::new(
                            BigInt::from(*r.numer()),
                            BigInt::from(*r.denom()),
                        )),
                        _ => None,
                    }
                };
                if let (Some(a), Some(b)) = (as_big(&lhs_kind), as_big(&rhs_kind)) {
                    return self.mk_bool(a == b);
                }
            }
            // String literals, for the same reason and in the same direction
            // as the numeric arms above. Their absence was a soundness bug,
            // not a missed optimisation: `nixie-solver` wires no string
            // theory, so an unfolded `(= "a" "b")` atom is a free Boolean the
            // SAT layer may set true, and `(or (= "a" "b") p) /\ ~p` answered
            // `sat`. Two distinct string literals are distinct values by
            // construction, exactly as two `IntConst` terms are.
            (Some(TermKind::StringLit(a)), Some(TermKind::StringLit(b))) => {
                return self.mk_bool(a == b);
            }
            // Boolean constants
            (Some(TermKind::True), Some(TermKind::True)) => return self.true_id,
            (Some(TermKind::False), Some(TermKind::False)) => return self.true_id,
            (Some(TermKind::True), Some(TermKind::False)) => return self.false_id,
            (Some(TermKind::False), Some(TermKind::True)) => return self.false_id,
            // BitVec constants
            (
                Some(TermKind::BitVecConst {
                    value: v1,
                    width: w1,
                }),
                Some(TermKind::BitVecConst {
                    value: v2,
                    width: w2,
                }),
            ) => {
                return self.mk_bool(v1 == v2 && w1 == w2);
            }
            _ => {}
        }

        // Canonicalize order
        let (lhs, rhs) = if lhs.0 <= rhs.0 {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        };

        let sort = self.sorts.bool_sort;
        self.intern(TermKind::Eq(lhs, rhs), sort)
    }

    /// Create a distinct constraint
    pub fn mk_distinct(&mut self, args: impl IntoIterator<Item = TermId>) -> TermId {
        let args: SmallVec<[TermId; 4]> = args.into_iter().collect();

        if args.len() <= 1 {
            return self.true_id;
        }

        let sort = self.sorts.bool_sort;
        self.intern(TermKind::Distinct(args), sort)
    }

    /// Create an addition
    ///
    /// Folds the numeral arguments at construction time (Z3's
    /// `arith_rewriter::mk_add_core`): the `IntConst` arguments are summed
    /// exactly in `BigInt` into a single numeral, the `RealConst` arguments
    /// into a single `RealConst` when the exact sum is representable.  This is
    /// what keeps a wide sum like `9223372036854775807 + 1` from ever reaching
    /// the `Rational64` tableau as two separately-fitting summands (where the
    /// fold would overflow) – it arrives as the one exact `IntConst(2^63)`
    /// instead, and the big-constant abstraction owns it from there.
    pub fn mk_add(&mut self, args: impl IntoIterator<Item = TermId>) -> TermId {
        let args: SmallVec<[TermId; 4]> = args.into_iter().collect();

        match args.len() {
            0 => self.mk_int(0),
            1 => args[0],
            _ => {
                let sort = unified_arith_sort(args[0], &args, self);
                // Classify once: integer numerals, real numerals, the rest.
                let mut int_sum: Option<BigInt> = None;
                let mut real_sum: Option<BigRational> = None;
                let mut others: SmallVec<[TermId; 4]> = SmallVec::new();
                let mut saw_int = false;
                let mut saw_real = false;
                for &a in &args {
                    if let Some(v) = int_const_of(a, self) {
                        saw_int = true;
                        int_sum = match int_sum.take() {
                            Some(s) => Some(s + v),
                            None => Some(v),
                        };
                    } else if let Some(v) = real_const_of(a, self) {
                        saw_real = true;
                        real_sum = match real_sum.take() {
                            Some(s) => Some(s + v),
                            None => Some(v),
                        };
                    } else {
                        others.push(a);
                    }
                }
                if !saw_int && !saw_real {
                    return self.intern(TermKind::Add(args), sort);
                }
                // Exact-but-unrepresentable real sum: keep the original real
                // operands (folding only the integer part stays exact).
                let folded_real = real_sum.and_then(narrow_rational);
                if saw_real && folded_real.is_none() {
                    // Re-run the classification keeping the real numerals.
                    others = args
                        .iter()
                        .copied()
                        .filter(|&a| int_const_of(a, self).is_none())
                        .collect();
                }
                let mut new_args = others;
                if let Some(r) = folded_real {
                    new_args.push(self.mk_real(r));
                }
                match int_sum {
                    // No integer numerals at all.
                    None => {
                        if new_args.len() == 1 {
                            new_args[0]
                        } else if new_args.is_empty() {
                            // Every argument was a real numeral and the sum
                            // folded; representable by construction above.
                            self.mk_real(folded_real.unwrap_or(Rational64::zero()))
                        } else {
                            self.intern(TermKind::Add(new_args), sort)
                        }
                    }
                    Some(s) if new_args.is_empty() => self.mk_int(s),
                    Some(s) if !s.is_zero() => {
                        new_args.push(self.mk_int(s));
                        self.intern(TermKind::Add(new_args), sort)
                    }
                    // The integer sum vanished: `(+ x 1 -1)` is `x` (or the
                    // remaining non-numeral args).
                    Some(_) => {
                        if new_args.len() == 1 {
                            new_args[0]
                        } else {
                            self.intern(TermKind::Add(new_args), sort)
                        }
                    }
                }
            }
        }
    }

    /// Create a subtraction
    ///
    /// Folds when both operands are numerals of the same family (exact in
    /// `BigInt` / `BigRational`); a non-uniform pair keeps its shape.
    pub fn mk_sub(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let sort = unified_arith_sort(lhs, &[lhs, rhs], self);
        if let (Some(a), Some(b)) = (int_const_of(lhs, self), int_const_of(rhs, self)) {
            return self.mk_int(a - b);
        }
        if sort == self.sorts.real_sort
            && let (Some(a), Some(b)) = (real_const_of(lhs, self), real_const_of(rhs, self))
            && let Some(r) = narrow_rational(a - b)
        {
            return self.mk_real(r);
        }
        self.intern(TermKind::Sub(lhs, rhs), sort)
    }

    /// Create arithmetic negation
    ///
    /// Folds a numeral operand to its exact negation.
    pub fn mk_neg(&mut self, arg: TermId) -> TermId {
        let sort = self.get(arg).map_or(self.sorts.int_sort, |t| t.sort);
        if let Some(v) = int_const_of(arg, self) {
            return self.mk_int(-v);
        }
        if sort == self.sorts.real_sort
            && let Some(r) = real_const_of(arg, self)
            && let Some(r) = narrow_rational(-r)
        {
            return self.mk_real(r);
        }
        self.intern(TermKind::Neg(arg), sort)
    }

    /// Create a multiplication
    ///
    /// Folds the numeral arguments at construction time: the `IntConst`
    /// arguments into their exact `BigInt` product (a zero product collapses
    /// the whole node to the zero of the node's sort), the `RealConst`
    /// arguments into a single `RealConst` when exactly representable.
    pub fn mk_mul(&mut self, args: impl IntoIterator<Item = TermId>) -> TermId {
        let args: SmallVec<[TermId; 4]> = args.into_iter().collect();

        match args.len() {
            0 => self.mk_int(1),
            1 => args[0],
            _ => {
                let sort = unified_arith_sort(args[0], &args, self);
                // Exact integer product of the IntConst arguments.
                let mut int_prod: Option<BigInt> = None;
                let mut rest: SmallVec<[TermId; 4]> = SmallVec::new();
                for &a in &args {
                    match int_const_of(a, self) {
                        Some(v) => {
                            int_prod = match int_prod.take() {
                                Some(s) => Some(s * v),
                                None => Some(v),
                            };
                        }
                        None => rest.push(a),
                    }
                }
                let mut real_prod: Option<BigRational> = None;
                let mut keep: SmallVec<[TermId; 4]> = SmallVec::new();
                let mut saw_real = false;
                for a in rest {
                    match real_const_of(a, self) {
                        Some(v) => {
                            saw_real = true;
                            real_prod = match real_prod.take() {
                                Some(s) => Some(s * v),
                                None => Some(v),
                            };
                        }
                        None => keep.push(a),
                    }
                }
                // Zero of either numeral family collapses the product to the
                // zero OF THE NODE'S SORT (`(* 0 1.5)` is `0.0`, not `0`).
                let int_zero = int_prod.as_ref().is_some_and(BigInt::is_zero);
                let real_zero = real_prod.as_ref().is_some_and(BigRational::is_zero);
                if int_zero || real_zero {
                    return if sort == self.sorts.real_sort {
                        self.mk_real(Rational64::zero())
                    } else {
                        self.mk_int(0)
                    };
                }
                let folded_real = real_prod.and_then(narrow_rational);
                if saw_real && folded_real.is_none() {
                    // Exact but unrepresentable: keep the original real
                    // operands (dropping them would change the value).
                    keep = args
                        .iter()
                        .copied()
                        .filter(|&a| int_const_of(a, self).is_none())
                        .collect();
                }
                if let Some(r) = folded_real {
                    keep.push(self.mk_real(r));
                }
                match int_prod {
                    None => {
                        if keep.len() == 1 {
                            keep[0]
                        } else if keep.is_empty() {
                            // Real numerals folded away entirely cannot happen
                            // (zero returned above); defensive.
                            self.mk_real(Rational64::one())
                        } else {
                            self.intern(TermKind::Mul(keep), sort)
                        }
                    }
                    // No surviving factors: the product IS the numeral.
                    Some(p) if keep.is_empty() => self.mk_int(p),
                    Some(p) if !p.is_one() => {
                        keep.push(self.mk_int(p));
                        self.intern(TermKind::Mul(keep), sort)
                    }
                    // Unit integer product: the numeral arguments vanish.
                    Some(_) => {
                        if keep.len() == 1 {
                            keep[0]
                        } else {
                            self.intern(TermKind::Mul(keep), sort)
                        }
                    }
                }
            }
        }
    }

    /// Create a division
    ///
    /// `mk_div` is the **`div`** (integer, Euclidean) constructor: the
    /// node's sort follows the unified operand sort, and two integer
    /// numerals fold to the exact `div_euclid` quotient – the same
    /// semantics the theory's defining axioms assert, so the folder and the
    /// axiomatiser agree on every value.  A zero divisor never folds
    /// (SMT-LIB: uninterpreted).  For SMT-LIB **`/`** (real division, whose
    /// result is `Real` even over `Int` operands) use [`Self::mk_rdiv`].
    pub fn mk_div(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        self.mk_div_at(lhs, rhs, false)
    }

    /// Create SMT-LIB **real division** (`/`): the result is `Real`-sorted
    /// even when both operands are `Int`-sorted (`Int` is a subsort of
    /// `Real`, so `(/ 7 2)` is the rational `7/2`, not Euclidean `3`).
    ///
    /// Routing `/` through the integer constructor was a silent
    /// wrong-semantics class: `(/ 7 2) = 3` came back `sat` (should be
    /// `unsat`) and `(/ 7 2) > 3` came back `unsat` (should be `sat`).
    ///
    /// Folding mirrors the real division path of the shared constructor: two numerals
    /// fold to the exact `BigRational` quotient; division by a nonzero
    /// numeral constant linearizes into multiplication by its exact
    /// reciprocal (`(/ x c) ≡ (* x (1/c))`, Z3's `arith_rewriter` policy),
    /// which makes it decidable; a symbolic or zero divisor keeps the
    /// `Div` node (zero: uninterpreted per SMT-LIB).
    pub fn mk_rdiv(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        self.mk_div_at(lhs, rhs, true)
    }

    /// The shared division constructor.  `force_real` selects SMT-LIB `/`
    /// semantics (result sort `Real`) over `div` semantics (unified operand
    /// sort); the parser chooses per the operator token.
    fn mk_div_at(&mut self, lhs: TermId, rhs: TermId, force_real: bool) -> TermId {
        let sort = if force_real {
            self.sorts.real_sort
        } else {
            unified_arith_sort(lhs, &[lhs, rhs], self)
        };
        if sort == self.sorts.int_sort
            && let (Some(a), Some(b)) = (int_const_of(lhs, self), int_const_of(rhs, self))
            && !b.is_zero()
        {
            // Euclidean division: the unique `q` with `m = n·q + r`,
            // `0 ≤ r < |n|` — exactly the defining axiom pair `arith_axioms`
            // asserts for `(div m n)`.
            return self.mk_int(a.div_euclid(&b));
        }
        if sort == self.sorts.real_sort {
            let a =
                real_const_of(lhs, self).or_else(|| int_const_of(lhs, self).map(BigRational::from));
            let b =
                real_const_of(rhs, self).or_else(|| int_const_of(rhs, self).map(BigRational::from));
            if let (Some(a), Some(b_ref)) = (a.as_ref(), b.as_ref())
                && !b_ref.is_zero()
                && let Some(r) = narrow_rational(a / b_ref)
            {
                return self.mk_real(r);
            }
            // Real division by a NONZERO CONSTANT linearizes exactly:
            // `(/ x c) ≡ (* x (1/c))` in the rationals (Z3's `arith_rewriter`
            // does the same rewrite).  This is what makes real division by
            // numerals DECIDABLE — the reciprocal of a `Rational64` is its
            // numerator/denominator swap, so it is always representable —
            // where the bare `Div` node is deliberately left undefined by
            // `arith_axioms` (its defining identity `x = y·q` is nonlinear)
            // and every atom mentioning it gates to `unknown`.  A symbolic
            // or zero divisor keeps the `Div` node (zero: uninterpreted per
            // SMT-LIB).
            if let Some(c) = b.filter(|c| !c.is_zero())
                && let Some(recip) = narrow_rational(BigRational::from(BigInt::from(1)) / c)
            {
                let recip_term = self.mk_real(recip);
                return self.mk_mul([lhs, recip_term]);
            }
        }
        self.intern(TermKind::Div(lhs, rhs), sort)
    }

    /// Create a modulo operation
    ///
    /// Folds to the exact **Euclidean** remainder (`rem_euclid` – always in
    /// `[0, |n|)`, the semantics the theory's axioms assert) on two integer
    /// numerals with a non-zero divisor.  `(mod m 0)` never folds (SMT-LIB:
    /// uninterpreted).
    pub fn mk_mod(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let sort = self.get(lhs).map_or(self.sorts.int_sort, |t| t.sort);
        if let (Some(a), Some(b)) = (int_const_of(lhs, self), int_const_of(rhs, self))
            && !b.is_zero()
        {
            // Euclidean remainder: `0 ≤ r < |n|` by construction, matching
            // the `mod` defining axioms.
            return self.mk_int(a.rem_euclid(&b));
        }
        self.intern(TermKind::Mod(lhs, rhs), sort)
    }

    /// Create a less-than comparison
    pub fn mk_lt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if let Some(ord) = numeric_cmp_fold(lhs, rhs, self) {
            return self.mk_bool(ord == core::cmp::Ordering::Less);
        }
        // Irreflexivity, on hash-consed identity (the same rule
        // `mk_str_lt` applies; Z3's `arith_rewriter` folds these too).
        if lhs == rhs {
            return self.mk_false();
        }
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::Lt(lhs, rhs), sort)
    }

    /// Create a less-than-or-equal comparison
    pub fn mk_le(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if let Some(ord) = numeric_cmp_fold(lhs, rhs, self) {
            return self.mk_bool(ord != core::cmp::Ordering::Greater);
        }
        // Reflexivity, on hash-consed identity.
        if lhs == rhs {
            return self.mk_true();
        }
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::Le(lhs, rhs), sort)
    }

    /// Create a greater-than comparison
    pub fn mk_gt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if let Some(ord) = numeric_cmp_fold(lhs, rhs, self) {
            return self.mk_bool(ord == core::cmp::Ordering::Greater);
        }
        // Irreflexivity, on hash-consed identity.
        if lhs == rhs {
            return self.mk_false();
        }
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::Gt(lhs, rhs), sort)
    }

    /// Create a greater-than-or-equal comparison
    pub fn mk_ge(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if let Some(ord) = numeric_cmp_fold(lhs, rhs, self) {
            return self.mk_bool(ord != core::cmp::Ordering::Less);
        }
        // Reflexivity, on hash-consed identity.  This one decides the
        // tautological-quantifier class (`forall u. u >= u` used to burn
        // every MBQI round enumerating no-op instances and end `unknown`).
        if lhs == rhs {
            return self.mk_true();
        }
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::Ge(lhs, rhs), sort)
    }

    /// Create a greater-than-or-equal comparison (alias for mk_ge)
    pub fn mk_geq(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        self.mk_ge(lhs, rhs)
    }

    /// Create a less-than-or-equal comparison (alias for mk_le)
    pub fn mk_leq(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        self.mk_le(lhs, rhs)
    }

    /// Create an array select operation
    pub fn mk_select(&mut self, array: TermId, index: TermId) -> TermId {
        // Get the range sort from the array's sort
        let sort = if let Some(term) = self.get(array) {
            if let Some(array_sort) = self.sorts.get(term.sort) {
                if let crate::sort::SortKind::Array { range, .. } = array_sort.kind {
                    range
                } else {
                    self.sorts.int_sort
                }
            } else {
                self.sorts.int_sort
            }
        } else {
            self.sorts.int_sort
        };
        self.intern(TermKind::Select(array, index), sort)
    }

    /// The empty set at element sort `element`.
    pub fn mk_set_empty(&mut self, element: SortId) -> TermId {
        let sort = self.sorts.set(element);
        self.intern(TermKind::SetEmpty(sort), sort)
    }

    /// The empty set, given its already-formed **set** sort.
    ///
    /// Used when rebuilding a term whose sort is already known; prefer
    /// [`TermManager::mk_set_empty`], which takes the *element* sort.
    pub fn mk_set_empty_at(&mut self, set_sort: SortId) -> TermId {
        self.intern(TermKind::SetEmpty(set_sort), set_sort)
    }

    /// `(set.singleton x)`.
    pub fn mk_set_singleton(&mut self, element: TermId) -> TermId {
        let elem_sort = self.get(element).map_or(self.sorts.int_sort, |t| t.sort);
        let sort = self.sorts.set(elem_sort);
        self.intern(TermKind::SetSingleton(element), sort)
    }

    /// `(set.union a b)`.
    pub fn mk_set_union(&mut self, a: TermId, b: TermId) -> TermId {
        let sort = self.set_result_sort(a);
        self.intern(TermKind::SetUnion(a, b), sort)
    }

    /// `(set.inter a b)`.
    pub fn mk_set_inter(&mut self, a: TermId, b: TermId) -> TermId {
        let sort = self.set_result_sort(a);
        self.intern(TermKind::SetInter(a, b), sort)
    }

    /// `(set.minus a b)`.
    pub fn mk_set_minus(&mut self, a: TermId, b: TermId) -> TermId {
        let sort = self.set_result_sort(a);
        self.intern(TermKind::SetMinus(a, b), sort)
    }

    /// `(set.member x s)`.
    pub fn mk_set_member(&mut self, element: TermId, set: TermId) -> TermId {
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::SetMember(element, set), sort)
    }

    /// `(set.subset a b)`.
    pub fn mk_set_subset(&mut self, a: TermId, b: TermId) -> TermId {
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::SetSubset(a, b), sort)
    }

    /// `(set.card s)`.
    pub fn mk_set_card(&mut self, set: TermId) -> TermId {
        let sort = self.sorts.int_sort;
        self.intern(TermKind::SetCard(set), sort)
    }

    /// The sort a homogeneous binary set operator returns: its first operand's.
    ///
    /// A non-set operand is a caller error the type rules catch; falling back
    /// to `Set(Int)` here keeps the builder total without inventing a *scalar*
    /// sort for something that is structurally a set.
    fn set_result_sort(&mut self, a: TermId) -> SortId {
        match self.get(a).map(|t| t.sort) {
            Some(s) if self.sorts.get(s).is_some_and(crate::sort::Sort::is_set) => s,
            _ => {
                let int = self.sorts.int_sort;
                self.sorts.set(int)
            }
        }
    }

    /// Create an array store operation
    pub fn mk_store(&mut self, array: TermId, index: TermId, value: TermId) -> TermId {
        let sort = self.get(array).map_or(self.sorts.int_sort, |t| t.sort);
        self.intern(TermKind::Store(array, index, value), sort)
    }

    /// Create a string literal
    pub fn mk_string_lit(&mut self, value: &str) -> TermId {
        let string_sort = self.sorts.string_sort();
        self.intern(TermKind::StringLit(value.to_string()), string_sort)
    }

    /// Create a string concatenation
    pub fn mk_str_concat(&mut self, s1: TermId, s2: TermId) -> TermId {
        let string_sort = self.sorts.string_sort();
        self.intern(TermKind::StrConcat(s1, s2), string_sort)
    }

    /// Create a string length operation
    pub fn mk_str_len(&mut self, s: TermId) -> TermId {
        let int_sort = self.sorts.int_sort;
        self.intern(TermKind::StrLen(s), int_sort)
    }

    /// Create a substring operation
    pub fn mk_str_substr(&mut self, s: TermId, start: TermId, len: TermId) -> TermId {
        let string_sort = self.sorts.string_sort();
        self.intern(TermKind::StrSubstr(s, start, len), string_sort)
    }

    /// Create a character at index operation
    pub fn mk_str_at(&mut self, s: TermId, i: TermId) -> TermId {
        let string_sort = self.sorts.string_sort();
        self.intern(TermKind::StrAt(s, i), string_sort)
    }

    /// Create a contains substring operation
    pub fn mk_str_contains(&mut self, s: TermId, sub: TermId) -> TermId {
        let bool_sort = self.sorts.bool_sort;
        self.intern(TermKind::StrContains(s, sub), bool_sort)
    }

    /// Create a prefix check operation
    pub fn mk_str_prefixof(&mut self, prefix: TermId, s: TermId) -> TermId {
        let bool_sort = self.sorts.bool_sort;
        self.intern(TermKind::StrPrefixOf(prefix, s), bool_sort)
    }

    /// Create a suffix check operation
    pub fn mk_str_suffixof(&mut self, suffix: TermId, s: TermId) -> TermId {
        let bool_sort = self.sorts.bool_sort;
        self.intern(TermKind::StrSuffixOf(suffix, s), bool_sort)
    }

    /// Create an index of operation
    pub fn mk_str_indexof(&mut self, s: TermId, sub: TermId, offset: TermId) -> TermId {
        let int_sort = self.sorts.int_sort;
        self.intern(TermKind::StrIndexOf(s, sub, offset), int_sort)
    }

    /// Create a string replace operation
    pub fn mk_str_replace(&mut self, s: TermId, pattern: TermId, replacement: TermId) -> TermId {
        let string_sort = self.sorts.string_sort();
        self.intern(TermKind::StrReplace(s, pattern, replacement), string_sort)
    }

    /// Create a replace all operation
    pub fn mk_str_replace_all(
        &mut self,
        s: TermId,
        pattern: TermId,
        replacement: TermId,
    ) -> TermId {
        let string_sort = self.sorts.string_sort();
        self.intern(
            TermKind::StrReplaceAll(s, pattern, replacement),
            string_sort,
        )
    }

    /// `str.replace_re` – replace the leftmost shortest match of a regular
    /// language.
    ///
    /// The regex operand carries the reserved `RegLan` sort (see
    /// [`Self::reglan_sort`]); the theory compiles it with its Brzozowski
    /// derivative engine, so no folding happens here (`nixie-core` deliberately
    /// hosts no regex matcher – `str.in_re` is left symbolic for the same
    /// reason).
    pub fn mk_str_replace_re(&mut self, s: TermId, re: TermId, replacement: TermId) -> TermId {
        let string_sort = self.sorts.string_sort();
        self.intern(TermKind::StrReplaceRe(s, re, replacement), string_sort)
    }

    /// `str.replace_re_all` – replace every shortest non-empty match of a
    /// regular language, scanning left to right.
    pub fn mk_str_replace_re_all(&mut self, s: TermId, re: TermId, replacement: TermId) -> TermId {
        let string_sort = self.sorts.string_sort();
        self.intern(TermKind::StrReplaceReAll(s, re, replacement), string_sort)
    }

    /// `str.<` – strict lexicographic order over code points.
    ///
    /// Folded on constant operands, and simplified on the three shapes whose
    /// truth is fixed by the order's structure alone. Reference: Z3's
    /// `seq_rewriter.cpp` `mk_str_lt`, which applies the same empty-operand
    /// rules.
    pub fn mk_str_lt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Irreflexivity. Terms are hash-consed, so equal ids are the same term.
        if lhs == rhs {
            return self.mk_false();
        }
        if let (Some(a), Some(b)) = (self.string_lit_of(lhs), self.string_lit_of(rhs)) {
            return if str_fold::str_lt(&a, &b) {
                self.mk_true()
            } else {
                self.mk_false()
            };
        }
        // Nothing is strictly below the empty string, which is the minimum.
        if self.is_empty_string_lit(rhs) {
            return self.mk_false();
        }
        // `"" < b` iff `b` is not itself empty.
        if self.is_empty_string_lit(lhs) {
            let eq = self.mk_eq(lhs, rhs);
            return self.mk_not(eq);
        }
        let bool_sort = self.sorts.bool_sort;
        self.intern(TermKind::StrLt(lhs, rhs), bool_sort)
    }

    /// `str.<=` – the reflexive closure of [`Self::mk_str_lt`].
    pub fn mk_str_le(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if lhs == rhs {
            return self.mk_true();
        }
        if let (Some(a), Some(b)) = (self.string_lit_of(lhs), self.string_lit_of(rhs)) {
            return if str_fold::str_le(&a, &b) {
                self.mk_true()
            } else {
                self.mk_false()
            };
        }
        // The empty string is below everything.
        if self.is_empty_string_lit(lhs) {
            return self.mk_true();
        }
        // `a <= ""` iff `a` is itself empty.
        if self.is_empty_string_lit(rhs) {
            return self.mk_eq(lhs, rhs);
        }
        let bool_sort = self.sorts.bool_sort;
        self.intern(TermKind::StrLe(lhs, rhs), bool_sort)
    }

    /// `str.to_code` – the code point of a singleton string, `-1` otherwise.
    pub fn mk_str_to_code(&mut self, s: TermId) -> TermId {
        if let Some(value) = self.string_lit_of(s) {
            return self.mk_int(str_fold::str_to_code(&value));
        }
        let int_sort = self.sorts.int_sort;
        self.intern(TermKind::StrToCode(s), int_sort)
    }

    /// `str.from_code` – the singleton string for a code point in the
    /// theory's alphabet, `""` outside it.
    ///
    /// A surrogate code point is deliberately left unfolded; see
    /// [`str_fold::FromCode::Unrepresentable`].
    pub fn mk_str_from_code(&mut self, n: TermId) -> TermId {
        if let Some(TermKind::IntConst(value)) = self.get(n).map(|t| t.kind.clone()) {
            match str_fold::str_from_code(&value) {
                str_fold::FromCode::Char(c) => {
                    let mut text = String::new();
                    text.push(c);
                    return self.mk_string_lit(&text);
                }
                str_fold::FromCode::Empty => return self.mk_string_lit(""),
                str_fold::FromCode::Unrepresentable => {}
            }
        }
        let string_sort = self.sorts.string_sort();
        self.intern(TermKind::StrFromCode(n), string_sort)
    }

    /// The value of `term` when it is a string literal, else `None`.
    fn string_lit_of(&self, term: TermId) -> Option<String> {
        match self.get(term).map(|t| &t.kind) {
            Some(TermKind::StringLit(s)) => Some(s.clone()),
            _ => None,
        }
    }

    /// Whether `term` is the empty string literal.
    fn is_empty_string_lit(&self, term: TermId) -> bool {
        matches!(self.get(term).map(|t| &t.kind), Some(TermKind::StringLit(s)) if s.is_empty())
    }

    /// Create a string to integer conversion
    pub fn mk_str_to_int(&mut self, s: TermId) -> TermId {
        let int_sort = self.sorts.int_sort;
        self.intern(TermKind::StrToInt(s), int_sort)
    }

    /// Create an integer to string conversion
    pub fn mk_int_to_str(&mut self, i: TermId) -> TermId {
        let string_sort = self.sorts.string_sort();
        self.intern(TermKind::IntToStr(i), string_sort)
    }

    /// Create a string in regex operation
    pub fn mk_str_in_re(&mut self, s: TermId, re: TermId) -> TermId {
        let bool_sort = self.sorts.bool_sort;
        self.intern(TermKind::StrInRe(s, re), bool_sort)
    }

    // ======== Regular-expression (RegLan) terms ========
    //
    // The SMT-LIB Strings theory `RegLan` sort has no dedicated `SortKind`
    // variant (that enum is matched exhaustively across sibling crates, so it
    // cannot be extended here). Instead `RegLan` is modelled as a reserved,
    // interned built-in sort (`Uninterpreted("RegLan")`) obtained through the
    // regular sort-creation API, and each regex operator is represented as an
    // `Apply` node whose function symbol is the canonical SMT-LIB operator name
    // (`re.++`, `re.union`, ...). The reserved name never collides with a
    // user-declared sort because the parser rejects `RegLan` as a declarable
    // sort name. The strings theory (`nixie-theories`) recognises these nodes by
    // their function symbol and compiles them into a Brzozowski-derivative
    // regex for membership solving.

    /// Get (interning on first use) the reserved built-in `RegLan` sort used
    /// as the sort of every regular-expression term.
    pub fn reglan_sort(&mut self) -> SortId {
        let spur = self.intern_str("RegLan");
        self.sorts
            .intern(crate::sort::SortKind::Uninterpreted(spur))
    }

    /// Build a regular-expression operator node (`Apply` with the canonical
    /// SMT-LIB operator name and `RegLan` sort).
    fn mk_regex_op(&mut self, name: &str, args: impl IntoIterator<Item = TermId>) -> TermId {
        let sort = self.reglan_sort();
        self.mk_apply(name, args, sort)
    }

    /// `re.none` – the empty regular language.
    pub fn mk_re_none(&mut self) -> TermId {
        self.mk_regex_op("re.none", core::iter::empty())
    }

    /// `re.all` – the language of all strings.
    pub fn mk_re_all(&mut self) -> TermId {
        self.mk_regex_op("re.all", core::iter::empty())
    }

    /// `re.allchar` – the language of all single-character strings.
    pub fn mk_re_all_char(&mut self) -> TermId {
        self.mk_regex_op("re.allchar", core::iter::empty())
    }

    /// `str.to_re` – singleton language containing exactly one string.
    pub fn mk_str_to_re(&mut self, s: TermId) -> TermId {
        self.mk_regex_op("str.to_re", [s])
    }

    /// `re.++` – regular-language concatenation.
    pub fn mk_re_concat(&mut self, args: impl IntoIterator<Item = TermId>) -> TermId {
        self.mk_regex_op("re.++", args)
    }

    /// `re.union` – regular-language union.
    pub fn mk_re_union(&mut self, args: impl IntoIterator<Item = TermId>) -> TermId {
        self.mk_regex_op("re.union", args)
    }

    /// `re.inter` – regular-language intersection.
    pub fn mk_re_inter(&mut self, args: impl IntoIterator<Item = TermId>) -> TermId {
        self.mk_regex_op("re.inter", args)
    }

    /// `re.*` – Kleene star.
    pub fn mk_re_star(&mut self, re: TermId) -> TermId {
        self.mk_regex_op("re.*", [re])
    }

    /// `re.+` – Kleene plus (one or more).
    pub fn mk_re_plus(&mut self, re: TermId) -> TermId {
        self.mk_regex_op("re.+", [re])
    }

    /// `re.opt` – optional (zero or one).
    pub fn mk_re_opt(&mut self, re: TermId) -> TermId {
        self.mk_regex_op("re.opt", [re])
    }

    /// `re.comp` – complement.
    pub fn mk_re_comp(&mut self, re: TermId) -> TermId {
        self.mk_regex_op("re.comp", [re])
    }

    /// `re.diff` – difference of two regular languages.
    pub fn mk_re_diff(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        self.mk_regex_op("re.diff", [lhs, rhs])
    }

    /// `re.range` – the language of single-character strings between two
    /// one-character string literals (`lo` and `hi`, passed through as the
    /// operator's operands).
    pub fn mk_re_range(&mut self, lo: TermId, hi: TermId) -> TermId {
        self.mk_regex_op("re.range", [lo, hi])
    }

    /// `(_ re.^ n) re` – the regex repeated exactly `n` times. The repetition
    /// count is encoded as a leading `Int` operand.
    pub fn mk_re_power(&mut self, n: u32, re: TermId) -> TermId {
        let count = self.mk_int(n);
        self.mk_regex_op("re.^", [count, re])
    }

    /// `(_ re.loop lo hi) re` – the regex repeated between `lo` and `hi` times.
    /// The bounds are encoded as two leading `Int` operands.
    pub fn mk_re_loop(&mut self, lo: u32, hi: u32, re: TermId) -> TermId {
        let lo_t = self.mk_int(lo);
        let hi_t = self.mk_int(hi);
        self.mk_regex_op("re.loop", [lo_t, hi_t, re])
    }

    // Floating-point operations

    /// Create a floating-point literal from components
    pub fn mk_fp_lit(
        &mut self,
        sign: bool,
        exp: impl Into<BigInt>,
        sig: impl Into<BigInt>,
        eb: u32,
        sb: u32,
    ) -> TermId {
        let sort = self.sorts.float_sort(eb, sb);
        self.intern(
            TermKind::FpLit {
                sign,
                exp: exp.into(),
                sig: sig.into(),
                eb,
                sb,
            },
            sort,
        )
    }

    /// Create floating-point positive infinity
    pub fn mk_fp_plus_infinity(&mut self, eb: u32, sb: u32) -> TermId {
        let sort = self.sorts.float_sort(eb, sb);
        self.intern(TermKind::FpPlusInfinity { eb, sb }, sort)
    }

    /// Create floating-point negative infinity
    pub fn mk_fp_minus_infinity(&mut self, eb: u32, sb: u32) -> TermId {
        let sort = self.sorts.float_sort(eb, sb);
        self.intern(TermKind::FpMinusInfinity { eb, sb }, sort)
    }

    /// Create floating-point positive zero
    pub fn mk_fp_plus_zero(&mut self, eb: u32, sb: u32) -> TermId {
        let sort = self.sorts.float_sort(eb, sb);
        self.intern(TermKind::FpPlusZero { eb, sb }, sort)
    }

    /// Create floating-point negative zero
    pub fn mk_fp_minus_zero(&mut self, eb: u32, sb: u32) -> TermId {
        let sort = self.sorts.float_sort(eb, sb);
        self.intern(TermKind::FpMinusZero { eb, sb }, sort)
    }

    /// Create floating-point NaN
    pub fn mk_fp_nan(&mut self, eb: u32, sb: u32) -> TermId {
        let sort = self.sorts.float_sort(eb, sb);
        self.intern(TermKind::FpNaN { eb, sb }, sort)
    }

    /// Create floating-point absolute value
    pub fn mk_fp_abs(&mut self, arg: TermId) -> TermId {
        let default_sort = self.sorts.float32_sort();
        let sort = self.get(arg).map_or(default_sort, |t| t.sort);
        self.intern(TermKind::FpAbs(arg), sort)
    }

    /// Create floating-point negation
    pub fn mk_fp_neg(&mut self, arg: TermId) -> TermId {
        let default_sort = self.sorts.float32_sort();
        let sort = self.get(arg).map_or(default_sort, |t| t.sort);
        self.intern(TermKind::FpNeg(arg), sort)
    }

    /// Create floating-point square root
    pub fn mk_fp_sqrt(&mut self, rm: RoundingMode, arg: TermId) -> TermId {
        let default_sort = self.sorts.float32_sort();
        let sort = self.get(arg).map_or(default_sort, |t| t.sort);
        self.intern(TermKind::FpSqrt(rm, arg), sort)
    }

    /// Create floating-point round to integral
    pub fn mk_fp_round_to_integral(&mut self, rm: RoundingMode, arg: TermId) -> TermId {
        let default_sort = self.sorts.float32_sort();
        let sort = self.get(arg).map_or(default_sort, |t| t.sort);
        self.intern(TermKind::FpRoundToIntegral(rm, arg), sort)
    }

    /// Create floating-point addition
    pub fn mk_fp_add(&mut self, rm: RoundingMode, lhs: TermId, rhs: TermId) -> TermId {
        let default_sort = self.sorts.float32_sort();
        let sort = self.get(lhs).map_or(default_sort, |t| t.sort);
        self.intern(TermKind::FpAdd(rm, lhs, rhs), sort)
    }

    /// Create floating-point subtraction
    pub fn mk_fp_sub(&mut self, rm: RoundingMode, lhs: TermId, rhs: TermId) -> TermId {
        let default_sort = self.sorts.float32_sort();
        let sort = self.get(lhs).map_or(default_sort, |t| t.sort);
        self.intern(TermKind::FpSub(rm, lhs, rhs), sort)
    }

    /// Create floating-point multiplication
    pub fn mk_fp_mul(&mut self, rm: RoundingMode, lhs: TermId, rhs: TermId) -> TermId {
        let default_sort = self.sorts.float32_sort();
        let sort = self.get(lhs).map_or(default_sort, |t| t.sort);
        self.intern(TermKind::FpMul(rm, lhs, rhs), sort)
    }

    /// Create floating-point division
    pub fn mk_fp_div(&mut self, rm: RoundingMode, lhs: TermId, rhs: TermId) -> TermId {
        let default_sort = self.sorts.float32_sort();
        let sort = self.get(lhs).map_or(default_sort, |t| t.sort);
        self.intern(TermKind::FpDiv(rm, lhs, rhs), sort)
    }

    /// Create floating-point remainder
    pub fn mk_fp_rem(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let default_sort = self.sorts.float32_sort();
        let sort = self.get(lhs).map_or(default_sort, |t| t.sort);
        self.intern(TermKind::FpRem(lhs, rhs), sort)
    }

    /// Create floating-point minimum
    pub fn mk_fp_min(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let default_sort = self.sorts.float32_sort();
        let sort = self.get(lhs).map_or(default_sort, |t| t.sort);
        self.intern(TermKind::FpMin(lhs, rhs), sort)
    }

    /// Create floating-point maximum
    pub fn mk_fp_max(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let default_sort = self.sorts.float32_sort();
        let sort = self.get(lhs).map_or(default_sort, |t| t.sort);
        self.intern(TermKind::FpMax(lhs, rhs), sort)
    }

    /// Create floating-point less than or equal comparison
    pub fn mk_fp_leq(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::FpLeq(lhs, rhs), sort)
    }

    /// Create floating-point less than comparison
    pub fn mk_fp_lt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::FpLt(lhs, rhs), sort)
    }

    /// Create floating-point greater than or equal comparison
    pub fn mk_fp_geq(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::FpGeq(lhs, rhs), sort)
    }

    /// Create floating-point greater than comparison
    pub fn mk_fp_gt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::FpGt(lhs, rhs), sort)
    }

    /// Create floating-point equality comparison
    pub fn mk_fp_eq(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::FpEq(lhs, rhs), sort)
    }

    /// Create floating-point fused multiply-add: (x * y) + z
    pub fn mk_fp_fma(&mut self, rm: RoundingMode, x: TermId, y: TermId, z: TermId) -> TermId {
        let default_sort = self.sorts.float32_sort();
        let sort = self.get(x).map_or(default_sort, |t| t.sort);
        self.intern(TermKind::FpFma(rm, x, y, z), sort)
    }

    /// Create floating-point is-normal predicate
    pub fn mk_fp_is_normal(&mut self, arg: TermId) -> TermId {
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::FpIsNormal(arg), sort)
    }

    /// Create floating-point is-subnormal predicate
    pub fn mk_fp_is_subnormal(&mut self, arg: TermId) -> TermId {
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::FpIsSubnormal(arg), sort)
    }

    /// Create floating-point is-zero predicate
    pub fn mk_fp_is_zero(&mut self, arg: TermId) -> TermId {
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::FpIsZero(arg), sort)
    }

    /// Create floating-point is-infinite predicate
    pub fn mk_fp_is_infinite(&mut self, arg: TermId) -> TermId {
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::FpIsInfinite(arg), sort)
    }

    /// Create floating-point is-NaN predicate
    pub fn mk_fp_is_nan(&mut self, arg: TermId) -> TermId {
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::FpIsNaN(arg), sort)
    }

    /// Create floating-point is-negative predicate
    pub fn mk_fp_is_negative(&mut self, arg: TermId) -> TermId {
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::FpIsNegative(arg), sort)
    }

    /// Create floating-point is-positive predicate
    pub fn mk_fp_is_positive(&mut self, arg: TermId) -> TermId {
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::FpIsPositive(arg), sort)
    }

    /// Convert floating-point to another FP format
    pub fn mk_fp_to_fp(&mut self, rm: RoundingMode, arg: TermId, eb: u32, sb: u32) -> TermId {
        let sort = self.sorts.float_sort(eb, sb);
        self.intern(TermKind::FpToFp { rm, arg, eb, sb }, sort)
    }

    /// Convert floating-point to signed bitvector
    pub fn mk_fp_to_sbv(&mut self, rm: RoundingMode, arg: TermId, width: u32) -> TermId {
        let sort = self.sorts.bitvec(width);
        self.intern(TermKind::FpToSBV { rm, arg, width }, sort)
    }

    /// Convert floating-point to unsigned bitvector
    pub fn mk_fp_to_ubv(&mut self, rm: RoundingMode, arg: TermId, width: u32) -> TermId {
        let sort = self.sorts.bitvec(width);
        self.intern(TermKind::FpToUBV { rm, arg, width }, sort)
    }

    /// Convert floating-point to real
    pub fn mk_fp_to_real(&mut self, arg: TermId) -> TermId {
        let sort = self.sorts.real_sort;
        self.intern(TermKind::FpToReal(arg), sort)
    }

    /// Convert real to floating-point
    pub fn mk_real_to_fp(&mut self, rm: RoundingMode, arg: TermId, eb: u32, sb: u32) -> TermId {
        let sort = self.sorts.float_sort(eb, sb);
        self.intern(TermKind::RealToFp { rm, arg, eb, sb }, sort)
    }

    /// Convert signed bitvector to floating-point
    pub fn mk_sbv_to_fp(&mut self, rm: RoundingMode, arg: TermId, eb: u32, sb: u32) -> TermId {
        let sort = self.sorts.float_sort(eb, sb);
        self.intern(TermKind::SBVToFp { rm, arg, eb, sb }, sort)
    }

    /// Convert unsigned bitvector to floating-point
    pub fn mk_ubv_to_fp(&mut self, rm: RoundingMode, arg: TermId, eb: u32, sb: u32) -> TermId {
        let sort = self.sorts.float_sort(eb, sb);
        self.intern(TermKind::UBVToFp { rm, arg, eb, sb }, sort)
    }

    /// Create a function application
    pub fn mk_apply(
        &mut self,
        func: &str,
        args: impl IntoIterator<Item = TermId>,
        sort: SortId,
    ) -> TermId {
        let func_spur = self.intern_str(func);
        let args: SmallVec<[TermId; 4]> = args.into_iter().collect();
        self.intern(
            TermKind::Apply {
                func: func_spur,
                args,
            },
            sort,
        )
    }

    // Algebraic datatypes

    /// Create a datatype constructor application
    ///
    /// Constructs a datatype value using the specified constructor.
    /// For example, `cons(1, nil)` for a list.
    pub fn mk_dt_constructor(
        &mut self,
        constructor: &str,
        args: impl IntoIterator<Item = TermId>,
        sort: SortId,
    ) -> TermId {
        let constructor_spur = self.intern_str(constructor);
        let args: SmallVec<[TermId; 4]> = args.into_iter().collect();
        self.intern(
            TermKind::DtConstructor {
                constructor: constructor_spur,
                args,
            },
            sort,
        )
    }

    /// Create a datatype tester/discriminator
    ///
    /// Tests if a term was constructed with a specific constructor.
    /// For example, `is-cons(x)` tests if `x` is a cons cell.
    pub fn mk_dt_tester(&mut self, constructor: &str, arg: TermId) -> TermId {
        let constructor_spur = self.intern_str(constructor);
        let bool_sort = self.sorts.bool_sort;
        self.intern(
            TermKind::DtTester {
                constructor: constructor_spur,
                arg,
            },
            bool_sort,
        )
    }

    /// Create a datatype selector/accessor
    ///
    /// Extracts a field from a datatype value.
    /// For example, `head(x)` extracts the first element of a cons cell.
    pub fn mk_dt_selector(&mut self, selector: &str, arg: TermId, result_sort: SortId) -> TermId {
        let selector_spur = self.intern_str(selector);
        self.intern(
            TermKind::DtSelector {
                selector: selector_spur,
                arg,
            },
            result_sort,
        )
    }

    /// Create a universal quantifier without patterns
    pub fn mk_forall<'a>(
        &mut self,
        vars: impl IntoIterator<Item = (&'a str, SortId)>,
        body: TermId,
    ) -> TermId {
        self.mk_forall_with_patterns(vars, body, core::iter::empty::<Vec<TermId>>())
    }

    /// Create a universal quantifier with instantiation patterns
    ///
    /// Patterns are lists of terms that guide quantifier instantiation.
    /// Each pattern is a conjunction of terms that must match for instantiation.
    ///
    /// # Example
    /// ```ignore
    /// // (forall ((x Int)) (! (> (f x) 0) :pattern ((f x))))
    /// let x_var = manager.mk_var("x", int_sort);
    /// let fx = manager.mk_apply("f", [x_var], int_sort);
    /// let body = manager.mk_gt(fx, zero);
    /// let forall = manager.mk_forall_with_patterns(
    ///     [("x", int_sort)],
    ///     body,
    ///     [[fx]],  // pattern: (f x)
    /// );
    /// ```
    pub fn mk_forall_with_patterns<'a, P, Q>(
        &mut self,
        vars: impl IntoIterator<Item = (&'a str, SortId)>,
        body: TermId,
        patterns: P,
    ) -> TermId
    where
        P: IntoIterator<Item = Q>,
        Q: IntoIterator<Item = TermId>,
    {
        use crate::interner::Spur;
        let vars: SmallVec<[(Spur, SortId); 2]> = vars
            .into_iter()
            .map(|(name, sort)| (self.intern_str(name), sort))
            .collect();

        if vars.is_empty() {
            return body;
        }

        let patterns: SmallVec<[SmallVec<[TermId; 2]>; 2]> = patterns
            .into_iter()
            .map(|p| p.into_iter().collect())
            .collect();

        let sort = self.sorts.bool_sort;
        self.intern(
            TermKind::Forall {
                vars,
                body,
                patterns,
            },
            sort,
        )
    }

    /// Create an existential quantifier without patterns
    pub fn mk_exists<'a>(
        &mut self,
        vars: impl IntoIterator<Item = (&'a str, SortId)>,
        body: TermId,
    ) -> TermId {
        self.mk_exists_with_patterns(vars, body, core::iter::empty::<Vec<TermId>>())
    }

    /// Create an existential quantifier with instantiation patterns
    pub fn mk_exists_with_patterns<'a, P, Q>(
        &mut self,
        vars: impl IntoIterator<Item = (&'a str, SortId)>,
        body: TermId,
        patterns: P,
    ) -> TermId
    where
        P: IntoIterator<Item = Q>,
        Q: IntoIterator<Item = TermId>,
    {
        use crate::interner::Spur;
        let vars: SmallVec<[(Spur, SortId); 2]> = vars
            .into_iter()
            .map(|(name, sort)| (self.intern_str(name), sort))
            .collect();

        if vars.is_empty() {
            return body;
        }

        let patterns: SmallVec<[SmallVec<[TermId; 2]>; 2]> = patterns
            .into_iter()
            .map(|p| p.into_iter().collect())
            .collect();

        let sort = self.sorts.bool_sort;
        self.intern(
            TermKind::Exists {
                vars,
                body,
                patterns,
            },
            sort,
        )
    }

    /// Create a let expression
    pub fn mk_let<'a>(
        &mut self,
        bindings: impl IntoIterator<Item = (&'a str, TermId)>,
        body: TermId,
    ) -> TermId {
        use crate::interner::Spur;
        let bindings: SmallVec<[(Spur, TermId); 2]> = bindings
            .into_iter()
            .map(|(name, term)| (self.intern_str(name), term))
            .collect();

        if bindings.is_empty() {
            return body;
        }

        let sort = self.get(body).map_or(self.sorts.bool_sort, |t| t.sort);
        self.intern(TermKind::Let { bindings, body }, sort)
    }

    // BitVector operations

    /// Create a bit vector concatenation.
    ///
    /// Both operands must have a bit-vector sort – the result width is
    /// exactly their sum, per SMT-LIB `FixedSizeBitVectors` semantics.
    /// Callers (in particular the SMT-LIB parser, which only ever applies
    /// `concat` to already sort-checked bit-vector terms) must guarantee
    /// this precondition. In debug builds a violation is caught immediately
    /// via `debug_assert!` rather than being silently absorbed: this
    /// function previously defaulted an unresolvable operand's width to a
    /// fabricated `32`, which could hide a genuine type error behind a
    /// plausible-looking but wrong-width result. `mk_bv_concat` has no
    /// `Result` return type to propagate a proper error through (and
    /// changing its signature would ripple across every existing caller),
    /// so release builds keep the historical `32` fallback as a last
    /// resort rather than panicking on malformed input.
    pub fn mk_bv_concat(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        self.try_mk_bv_concat(lhs, rhs)
            .unwrap_or_else(|_| self.mk_bv_concat_fallback(lhs, rhs))
    }

    /// The checked form of [`TermManager::mk_bv_concat`].
    ///
    /// The infallible version defaulted an unresolvable operand's width to a
    /// fabricated `32` in release builds; a fabricated width is not cosmetic,
    /// because it interns a well-formed term at the wrong sort, which can
    /// flip a query between `sat` and `unsat`.  The checked function returns
    /// `NixieError::SortMismatchSimple` naming both operand sorts.
    /// (Ported from upstream v0.3.3.)
    pub fn try_mk_bv_concat(
        &mut self,
        lhs: TermId,
        rhs: TermId,
    ) -> Result<TermId, crate::error::NixieError> {
        let lhs_width = self
            .get(lhs)
            .and_then(|t| self.sorts.get(t.sort))
            .and_then(|s| s.bitvec_width());
        let rhs_width = self
            .get(rhs)
            .and_then(|t| self.sorts.get(t.sort))
            .and_then(|s| s.bitvec_width());
        let (Some(lhs_width), Some(rhs_width)) = (lhs_width, rhs_width) else {
            let sort_name = |t: TermId| -> String {
                self.get(t)
                    .and_then(|d| self.sorts.sort_name(d.sort))
                    .unwrap_or_else(|| "?".to_string())
            };
            let (lhs_sort, rhs_sort) = (sort_name(lhs), sort_name(rhs));
            return Err(crate::error::NixieError::SortMismatchSimple {
                expected: format!("(_ BitVec w) for concat lhs ({lhs_sort})"),
                found: format!("(_ BitVec w) for concat rhs ({rhs_sort})"),
            });
        };
        Ok(self.mk_bv_concat_checked(lhs, rhs, lhs_width, rhs_width))
    }

    /// `mk_bv_concat` over operands whose widths are already resolved.
    fn mk_bv_concat_checked(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        lhs_width: u32,
        rhs_width: u32,
    ) -> TermId {
        let width = lhs_width + rhs_width;

        // Both halves literal: splice them into a single literal.
        if let (Some(lhs_value), Some(rhs_value)) = (
            self.bv_const_unsigned(lhs, lhs_width),
            self.bv_const_unsigned(rhs, rhs_width),
        ) {
            return self.mk_bitvec(bv_fold::bv_concat(&lhs_value, &rhs_value, rhs_width), width);
        }

        let sort = self.sorts.bitvec(width);
        self.intern(TermKind::BvConcat(lhs, rhs), sort)
    }

    /// Historical infallible `mk_bv_concat` body: keeps the debug-time
    /// diagnosis and the release `32` fallback for existing callers that
    /// cannot propagate an error (the sort-checked parser paths), while the
    /// substitution/ematching paths move to the checked form.
    fn mk_bv_concat_fallback(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let lhs_width = self
            .get(lhs)
            .and_then(|t| self.sorts.get(t.sort))
            .and_then(|s| s.bitvec_width());
        let rhs_width = self
            .get(rhs)
            .and_then(|t| self.sorts.get(t.sort))
            .and_then(|s| s.bitvec_width());
        debug_assert!(
            lhs_width.is_some() && rhs_width.is_some(),
            "mk_bv_concat: both operands must have a bit-vector sort (lhs_width={lhs_width:?}, rhs_width={rhs_width:?})"
        );
        match (lhs_width, rhs_width) {
            (Some(lw), Some(rw)) => self.mk_bv_concat_checked(lhs, rhs, lw, rw),
            (lw, rw) => {
                // Release-build last resort, unchanged from history: fabricate
                // the historical 32 for an unresolvable operand rather than
                // panicking on malformed input.  Every producer of terms goes
                // through the sort checker first; only already-malformed input
                // can reach this.
                let width = lw.unwrap_or(32) + rw.unwrap_or(32);
                let sort = self.sorts.bitvec(width);
                self.intern(TermKind::BvConcat(lhs, rhs), sort)
            }
        }
    }

    /// Create a bit vector NAND: `bvnand(a, b) = bvnot(bvand(a, b))`.
    pub fn mk_bv_nand(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let and = self.mk_bv_and(lhs, rhs);
        self.mk_bv_not(and)
    }

    /// Create a bit vector NOR: `bvnor(a, b) = bvnot(bvor(a, b))`.
    pub fn mk_bv_nor(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let or = self.mk_bv_or(lhs, rhs);
        self.mk_bv_not(or)
    }

    /// Create a bit vector XNOR: `bvxnor(a, b) = bvnot(bvxor(a, b))`.
    pub fn mk_bv_xnor(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let xor = self.mk_bv_xor(lhs, rhs);
        self.mk_bv_not(xor)
    }

    /// Create a bit vector comparison: a 1-bit result that is `#b1` when
    /// the two (equal-width) operands are equal and `#b0` otherwise, per
    /// SMT-LIB `FixedSizeBitVectors` `bvcomp`.
    pub fn mk_bv_comp(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let eq = self.mk_eq(lhs, rhs);
        let one = self.mk_bitvec(1i64, 1);
        let zero = self.mk_bitvec(0i64, 1);
        self.mk_ite(eq, one, zero)
    }

    /// Create a signed bit-vector modulo (`bvsmod`), whose result sign
    /// follows the *divisor* `rhs` – distinct from `bvsrem`, whose result
    /// sign follows the dividend. Implements the standard SMT-LIB
    /// `FixedSizeBitVectors` definition by reducing to the unsigned
    /// remainder over the operands' absolute values and then reintroducing
    /// the sign according to the operand-sign combination:
    ///
    /// ```text
    /// u = bvurem(abs(s), abs(t))
    /// bvsmod(s, t) = u                    if u = 0
    ///              = u                    if sign(s) = sign(t) = +
    ///              = -u + t               if sign(s) = -, sign(t) = +
    ///              = u + t                if sign(s) = +, sign(t) = -
    ///              = -u                   if sign(s) = sign(t) = -
    /// ```
    ///
    /// Two literal operands are folded directly instead of being expanded
    /// into that `ite` chain.  The chain would collapse to the same constant
    /// on its own (every condition becomes literal), but evaluating it here
    /// keeps the definition of the total zero-divisor case – `bvsmod s 0` is
    /// `s` – in one auditable place alongside the rest of the division
    /// family.
    pub fn mk_bv_smod(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let width = self
            .get(lhs)
            .and_then(|t| self.sorts.get(t.sort))
            .and_then(|s| s.bitvec_width())
            .unwrap_or(32);
        if width == 0 {
            return self.mk_bv_urem(lhs, rhs);
        }
        if let Some((lhs_value, rhs_value)) = self.bv_const_pair(lhs, rhs, width) {
            return self.mk_bitvec(bv_fold::bv_smod(&lhs_value, &rhs_value, width), width);
        }
        let msb = width - 1;
        let msb_s = self.mk_bv_extract(msb, msb, lhs);
        let msb_t = self.mk_bv_extract(msb, msb, rhs);
        let zero_bit = self.mk_bitvec(0i64, 1);
        let s_nonneg = self.mk_eq(msb_s, zero_bit);
        let t_nonneg = self.mk_eq(msb_t, zero_bit);
        let not_s_nonneg = self.mk_not(s_nonneg);
        let not_t_nonneg = self.mk_not(t_nonneg);

        let neg_s = self.mk_bv_neg(lhs);
        let neg_t = self.mk_bv_neg(rhs);
        let abs_s = self.mk_ite(s_nonneg, lhs, neg_s);
        let abs_t = self.mk_ite(t_nonneg, rhs, neg_t);
        let u = self.mk_bv_urem(abs_s, abs_t);

        let zero_w = self.mk_bitvec(0i64, width);
        let u_is_zero = self.mk_eq(u, zero_w);
        let neg_u = self.mk_bv_neg(u);
        let u_plus_t = self.mk_bv_add(u, rhs);
        let negu_plus_t = self.mk_bv_add(neg_u, rhs);

        let both_nonneg = self.mk_and([s_nonneg, t_nonneg]);
        let s_neg_t_nonneg = self.mk_and([not_s_nonneg, t_nonneg]);
        let s_nonneg_t_neg = self.mk_and([s_nonneg, not_t_nonneg]);

        // Innermost: both negative -> -u.
        let case_both_neg = neg_u;
        // s non-negative, t negative -> u + t.
        let case3 = self.mk_ite(s_nonneg_t_neg, u_plus_t, case_both_neg);
        // s negative, t non-negative -> -u + t.
        let case2 = self.mk_ite(s_neg_t_nonneg, negu_plus_t, case3);
        // Both non-negative -> u.
        let case1 = self.mk_ite(both_nonneg, u, case2);
        // u = 0 -> u.
        self.mk_ite(u_is_zero, u, case1)
    }

    /// Create a bit vector extraction.
    ///
    /// Callers (in particular the SMT-LIB parser lowering `(_ extract i j)`)
    /// must ensure `low <= high` and `high < width(arg)` *before* calling this
    /// so the resulting term is semantically meaningful. As defense in depth
    /// against malformed indices reaching this far (which would otherwise
    /// underflow `high - low + 1` – a panic in debug builds and a ~4-billion
    /// bit sort in release builds), the width computation uses checked
    /// arithmetic and falls back to a minimal 1-bit result instead of
    /// panicking or wrapping.
    pub fn mk_bv_extract(&mut self, high: u32, low: u32, arg: TermId) -> TermId {
        let width = high
            .checked_sub(low)
            .and_then(|span| span.checked_add(1))
            .unwrap_or(1);

        // A literal operand yields a literal slice, provided the indices are
        // in range – malformed indices are left for the parser's sort check
        // rather than silently folded to a fabricated value.
        if low <= high
            && let Some(arg_width) = self.bv_width_of(arg)
            && high < arg_width
            && let Some(value) = self.bv_const_unsigned(arg, arg_width)
        {
            return self.mk_bitvec(bv_fold::bv_extract(&value, high, low), width);
        }

        let sort = self.sorts.bitvec(width);
        self.intern(TermKind::BvExtract { high, low, arg }, sort)
    }

    /// Create a bit vector NOT.
    ///
    /// Folds a literal operand and collapses `bvnot (bvnot t)` to `t`.
    pub fn mk_bv_not(&mut self, arg: TermId) -> TermId {
        if let Some(width) = self.bv_width_of(arg).filter(|width| *width > 0) {
            if let Some(value) = self.bv_const_unsigned(arg, width) {
                return self.mk_bitvec(bv_fold::bv_not(&value, width), width);
            }
            // bvnot (bvnot t) -> t: complement is an involution.
            if let Some(term) = self.get(arg)
                && let TermKind::BvNot(inner) = term.kind
            {
                return inner;
            }
        }

        let sort = self.get(arg).map(|t| t.sort);
        let sort = sort.unwrap_or_else(|| self.sorts.bitvec(32));
        self.intern(TermKind::BvNot(arg), sort)
    }

    /// Create a bit vector AND.
    ///
    /// Folds two literals and applies `t & t -> t`, `t & 0 -> 0` and
    /// `t & all-ones -> t`.
    pub fn mk_bv_and(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let (lhs, rhs) = canonical_pair(lhs, rhs);
        if let Some(width) = self.bv_binop_width(lhs, rhs) {
            let (lhs_value, rhs_value) = self.bv_operand_consts(lhs, rhs, width);
            if let (Some(lhs_value), Some(rhs_value)) = (&lhs_value, &rhs_value) {
                return self.mk_bitvec(bv_fold::bv_and(lhs_value, rhs_value, width), width);
            }
            if lhs == rhs {
                return lhs;
            }
            let all_ones = bv_fold::all_ones(width);
            if let Some(lhs_value) = &lhs_value {
                if *lhs_value == BigInt::ZERO {
                    return lhs;
                }
                if *lhs_value == all_ones {
                    return rhs;
                }
            }
            if let Some(rhs_value) = &rhs_value {
                if *rhs_value == BigInt::ZERO {
                    return rhs;
                }
                if *rhs_value == all_ones {
                    return lhs;
                }
            }
        }

        let sort = self.get(lhs).map(|t| t.sort);
        let sort = sort.unwrap_or_else(|| self.sorts.bitvec(32));
        self.intern(TermKind::BvAnd(lhs, rhs), sort)
    }

    /// Create a bit vector OR.
    ///
    /// Folds two literals and applies `t | t -> t`, `t | 0 -> t` and
    /// `t | all-ones -> all-ones`.
    pub fn mk_bv_or(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let (lhs, rhs) = canonical_pair(lhs, rhs);
        if let Some(width) = self.bv_binop_width(lhs, rhs) {
            let (lhs_value, rhs_value) = self.bv_operand_consts(lhs, rhs, width);
            if let (Some(lhs_value), Some(rhs_value)) = (&lhs_value, &rhs_value) {
                return self.mk_bitvec(bv_fold::bv_or(lhs_value, rhs_value, width), width);
            }
            if lhs == rhs {
                return lhs;
            }
            let all_ones = bv_fold::all_ones(width);
            if let Some(lhs_value) = &lhs_value {
                if *lhs_value == BigInt::ZERO {
                    return rhs;
                }
                if *lhs_value == all_ones {
                    return lhs;
                }
            }
            if let Some(rhs_value) = &rhs_value {
                if *rhs_value == BigInt::ZERO {
                    return lhs;
                }
                if *rhs_value == all_ones {
                    return rhs;
                }
            }
        }

        let sort = self.get(lhs).map(|t| t.sort);
        let sort = sort.unwrap_or_else(|| self.sorts.bitvec(32));
        self.intern(TermKind::BvOr(lhs, rhs), sort)
    }

    /// Create a bit vector addition.
    ///
    /// Folds two literals and applies `t + 0 -> t`.
    pub fn mk_bv_add(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let (lhs, rhs) = canonical_pair(lhs, rhs);
        if let Some(width) = self.bv_binop_width(lhs, rhs) {
            let (lhs_value, rhs_value) = self.bv_operand_consts(lhs, rhs, width);
            if let (Some(lhs_value), Some(rhs_value)) = (&lhs_value, &rhs_value) {
                return self.mk_bitvec(bv_fold::bv_add(lhs_value, rhs_value, width), width);
            }
            if lhs_value.is_some_and(|value| value == BigInt::ZERO) {
                return rhs;
            }
            if rhs_value.is_some_and(|value| value == BigInt::ZERO) {
                return lhs;
            }
        }

        let sort = self.get(lhs).map(|t| t.sort);
        let sort = sort.unwrap_or_else(|| self.sorts.bitvec(32));
        self.intern(TermKind::BvAdd(lhs, rhs), sort)
    }

    /// Create a bit vector subtraction.
    ///
    /// Folds two literals and applies `t - t -> 0` and `t - 0 -> t`.
    pub fn mk_bv_sub(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if let Some(width) = self.bv_binop_width(lhs, rhs) {
            if let Some((lhs_value, rhs_value)) = self.bv_const_pair(lhs, rhs, width) {
                return self.mk_bitvec(bv_fold::bv_sub(&lhs_value, &rhs_value, width), width);
            }
            if lhs == rhs {
                return self.mk_bitvec(0i64, width);
            }
            if self
                .bv_const_unsigned(rhs, width)
                .is_some_and(|value| value == BigInt::ZERO)
            {
                return lhs;
            }
        }

        let sort = self.get(lhs).map(|t| t.sort);
        let sort = sort.unwrap_or_else(|| self.sorts.bitvec(32));
        self.intern(TermKind::BvSub(lhs, rhs), sort)
    }

    /// Create a bit vector multiplication.
    ///
    /// Folds two literals and applies `t * 0 -> 0` and `t * 1 -> t`.
    pub fn mk_bv_mul(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let (lhs, rhs) = canonical_pair(lhs, rhs);
        if let Some(width) = self.bv_binop_width(lhs, rhs) {
            let (lhs_value, rhs_value) = self.bv_operand_consts(lhs, rhs, width);
            if let (Some(lhs_value), Some(rhs_value)) = (&lhs_value, &rhs_value) {
                return self.mk_bitvec(bv_fold::bv_mul(lhs_value, rhs_value, width), width);
            }
            let one = BigInt::from(1u8);
            if let Some(lhs_value) = &lhs_value {
                if *lhs_value == BigInt::ZERO {
                    return lhs;
                }
                if *lhs_value == one {
                    return rhs;
                }
            }
            if let Some(rhs_value) = &rhs_value {
                if *rhs_value == BigInt::ZERO {
                    return rhs;
                }
                if *rhs_value == one {
                    return lhs;
                }
            }
        }

        let sort = self.get(lhs).map(|t| t.sort);
        let sort = sort.unwrap_or_else(|| self.sorts.bitvec(32));
        self.intern(TermKind::BvMul(lhs, rhs), sort)
    }

    /// Width of `term` when it is bit-vector sorted.
    fn bv_width_of(&self, term: TermId) -> Option<u32> {
        let sort = self.get(term)?.sort;
        self.sorts.get(sort)?.bitvec_width()
    }

    /// Value of `term` when it is a bit-vector literal, normalised into the
    /// unsigned range `[0, 2^width)`.
    fn bv_const_unsigned(&self, term: TermId, width: u32) -> Option<BigInt> {
        let TermKind::BitVecConst { value, .. } = &self.get(term)?.kind else {
            return None;
        };
        Some(bv_fold::bv_wrap_unsigned(value, width))
    }

    /// Both operands' values, when both are bit-vector literals.
    fn bv_const_pair(&self, lhs: TermId, rhs: TermId, width: u32) -> Option<(BigInt, BigInt)> {
        Some((
            self.bv_const_unsigned(lhs, width)?,
            self.bv_const_unsigned(rhs, width)?,
        ))
    }

    /// Each operand's value, or `None` where it is not a literal.
    ///
    /// Normalising a literal allocates, so the identity rules below take both
    /// values once from here instead of re-reading each operand per rule.
    fn bv_operand_consts(
        &self,
        lhs: TermId,
        rhs: TermId,
        width: u32,
    ) -> (Option<BigInt>, Option<BigInt>) {
        (
            self.bv_const_unsigned(lhs, width),
            self.bv_const_unsigned(rhs, width),
        )
    }

    /// The common width of a binary bit-vector operator's operands, when it is
    /// a usable (non-degenerate) bit-vector width.
    ///
    /// Constant folding is skipped for width `0`, which is not a legal
    /// SMT-LIB bit-vector sort and therefore never carries a meaningful value.
    fn bv_binop_width(&self, lhs: TermId, rhs: TermId) -> Option<u32> {
        self.bv_width_of(lhs)
            .or_else(|| self.bv_width_of(rhs))
            .filter(|width| *width > 0)
    }

    /// Decide a bit-vector comparison that holds (or fails) for *every*
    /// assignment, returning the constant truth value it folds to.
    ///
    /// Reference: Z3's `bv_rewriter.cpp`, which folds exactly these atoms.
    /// Without them, an assertion like `(bvult x #b00000000)` – false for every
    /// `x`, since nothing is unsigned-less-than zero – survives as an
    /// unconstrained boolean atom and the solver answers a spurious `sat`.
    ///
    /// The rules, for width `w` with `MAX_U = 2^w - 1`, `MIN_S = -2^(w-1)` and
    /// `MAX_S = 2^(w-1) - 1`:
    ///
    /// * `t <u t`, `t <s t` → `false`; `t <=u t`, `t <=s t` → `true`.
    /// * `t <u 0`, `MAX_U <u t`, `t <s MIN_S`, `MAX_S <s t` → `false`.
    /// * `0 <=u t`, `t <=u MAX_U`, `MIN_S <=s t`, `t <=s MAX_S` → `true`.
    /// * both operands literal → evaluate directly.
    ///
    /// `signed` selects the two's-complement order, `strict` selects `<` over
    /// `<=`.  Returns `None` when the atom is not decidable syntactically.
    fn fold_bv_compare(
        &self,
        lhs: TermId,
        rhs: TermId,
        signed: bool,
        strict: bool,
    ) -> Option<bool> {
        let width = self.bv_width_of(lhs).or_else(|| self.bv_width_of(rhs))?;
        if width == 0 {
            return None;
        }

        // Both orders are total and reflexive, so `t < t` is false and
        // `t <= t` is true for any term – hash-consing makes the syntactic
        // identity check exact.
        if lhs == rhs {
            return Some(!strict);
        }

        // Reinterpret an unsigned literal under the selected order.
        let in_order = |v: BigInt| -> BigInt {
            if signed && v >= (BigInt::from(1u8) << (width - 1) as usize) {
                v - (BigInt::from(1u8) << width as usize)
            } else {
                v
            }
        };
        let lhs_const = self.bv_const_unsigned(lhs, width).map(&in_order);
        let rhs_const = self.bv_const_unsigned(rhs, width).map(&in_order);

        if let (Some(l), Some(r)) = (&lhs_const, &rhs_const) {
            return Some(if strict { l < r } else { l <= r });
        }

        let (min_value, max_value) = if signed {
            (
                -(BigInt::from(1u8) << (width - 1) as usize),
                (BigInt::from(1u8) << (width - 1) as usize) - 1,
            )
        } else {
            (BigInt::ZERO, (BigInt::from(1u8) << width as usize) - 1)
        };

        if let Some(r) = &rhs_const {
            // `t < MIN` is unsatisfiable; `t <= MAX` is a tautology.
            if strict && *r == min_value {
                return Some(false);
            }
            if !strict && *r == max_value {
                return Some(true);
            }
        }
        if let Some(l) = &lhs_const {
            // `MAX < t` is unsatisfiable; `MIN <= t` is a tautology.
            if strict && *l == max_value {
                return Some(false);
            }
            if !strict && *l == min_value {
                return Some(true);
            }
        }

        None
    }

    /// Create a bit vector unsigned less-than
    pub fn mk_bv_ult(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if let Some(value) = self.fold_bv_compare(lhs, rhs, false, true) {
            return self.mk_bool(value);
        }
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::BvUlt(lhs, rhs), sort)
    }

    /// Create a bit vector signed less-than
    pub fn mk_bv_slt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if let Some(value) = self.fold_bv_compare(lhs, rhs, true, true) {
            return self.mk_bool(value);
        }
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::BvSlt(lhs, rhs), sort)
    }

    /// Create a bit vector unsigned less-than-or-equal
    pub fn mk_bv_ule(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if let Some(value) = self.fold_bv_compare(lhs, rhs, false, false) {
            return self.mk_bool(value);
        }
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::BvUle(lhs, rhs), sort)
    }

    /// Create a bit vector signed less-than-or-equal
    pub fn mk_bv_sle(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if let Some(value) = self.fold_bv_compare(lhs, rhs, true, false) {
            return self.mk_bool(value);
        }
        let sort = self.sorts.bool_sort;
        self.intern(TermKind::BvSle(lhs, rhs), sort)
    }

    /// Create a bit vector negation (two's complement).
    ///
    /// Lowered to `0 - arg` through [`Self::mk_bv_sub`], so a literal operand
    /// is folded by the same rule that folds subtraction.
    pub fn mk_bv_neg(&mut self, arg: TermId) -> TermId {
        // Get the width from the argument's sort
        let sort = self.get(arg).map_or(self.sorts.bool_sort, |t| t.sort);
        let width = self
            .sorts
            .get(sort)
            .and_then(|s| s.bitvec_width())
            .unwrap_or(32);
        let zero = self.mk_bitvec(0i64, width);
        self.mk_bv_sub(zero, arg)
    }

    /// Create an unsigned bit vector division.
    ///
    /// Folds two literals, including the **total** division-by-zero case
    /// `(bvudiv s (_ bv0 m))` = all ones.
    /// Create an unsigned bit vector division.
    ///
    /// Besides folding two literals (the total `bvudiv` semantics), the
    /// **constant-divisor identities** of Z3's `bv_rewriter::mk_bv_udiv_core`
    /// fire here so every layer (parser, preprocessing, rewriting) sees the
    /// already-collapsed form:
    ///
    /// * `x udiv 0` → all-ones (SMT-LIB hardware reading, matching
    ///   [`bv_fold::bv_udiv`]'s constant case);
    /// * `x udiv 1` → `x`;
    /// * `x udiv 2^k` → `x >>l k` — the rule that collapses the
    ///   quantization chains (`Sydr/cjpeg`: JPEG dequantization by powers
    ///   of two, where the width-64 divider networks were the entire
    ///   circuit budget) into a wire permutation with no divider at all.
    pub fn mk_bv_udiv(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if let Some(width) = self.bv_binop_width(lhs, rhs)
            && let Some((lhs_value, rhs_value)) = self.bv_const_pair(lhs, rhs, width)
        {
            return self.mk_bitvec(bv_fold::bv_udiv(&lhs_value, &rhs_value, width), width);
        }
        if let Some(width) = self.bv_binop_width(lhs, rhs)
            && let Some(c) = self.bv_const_unsigned(rhs, width)
        {
            if c == BigInt::ZERO {
                // x udiv 0 = all ones.
                let ones = BigInt::from(2u8).pow(width) - BigInt::from(1u8);
                return self.mk_bitvec(ones, width);
            }
            if c == BigInt::from(1u8) {
                return lhs;
            }
            if let Some(shift) = Self::power_of_two_exponent(&c, width) {
                let dist = self.mk_bitvec(BigInt::from(shift), width);
                return self.mk_bv_lshr(lhs, dist);
            }
        }
        let sort = self.get(lhs).map_or(self.sorts.bool_sort, |t| t.sort);
        self.intern(TermKind::BvUdiv(lhs, rhs), sort)
    }

    /// Exponent `k` when `c` is a power of two with `1 <= 2^k < 2^width`
    /// (`k < width`; `2^width` itself is out of range after constant
    /// normalization).  `None` for non-powers, zero, and one (a shift by 0
    /// would be the identity and is handled by the callers).
    fn power_of_two_exponent(c: &BigInt, width: u32) -> Option<u32> {
        debug_assert!(*c != BigInt::ZERO);
        if *c == BigInt::from(1u8) {
            return None;
        }
        let bits = c.bits();
        let candidate = BigInt::from(1u8) << (bits - 1) as usize;
        if *c == candidate && bits > 1 && bits - 1 < u64::from(width) {
            Some(bits as u32 - 1)
        } else {
            None
        }
    }

    /// Create a signed bit vector division.
    ///
    /// Folds two literals, including the **total** division-by-zero case
    /// `(bvsdiv s (_ bv0 m))` = `-1` for non-negative `s` and `1` otherwise.
    /// For a symbolic dividend the divisor identities of Z3's
    /// `mk_bv_sdiv_core` fire: `x sdiv 1 = x` and `x sdiv 0 =
    /// ite(x <s 0, 1, all-ones)` (the same total semantics the constant
    /// folder applies).
    pub fn mk_bv_sdiv(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if let Some(width) = self.bv_binop_width(lhs, rhs)
            && let Some((lhs_value, rhs_value)) = self.bv_const_pair(lhs, rhs, width)
        {
            return self.mk_bitvec(bv_fold::bv_sdiv(&lhs_value, &rhs_value, width), width);
        }
        if let Some(width) = self.bv_binop_width(lhs, rhs)
            && let Some(c) = self.bv_const_unsigned(rhs, width)
        {
            if c == BigInt::ZERO {
                // x sdiv 0 = ite(x <s 0, 1, all-ones).
                let one = self.mk_bitvec(1, width);
                let ones = BigInt::from(2u8).pow(width) - BigInt::from(1u8);
                let ones_term = self.mk_bitvec(ones, width);
                let zero = self.mk_bitvec(0, width);
                let negative = self.mk_bv_slt(lhs, zero);
                return self.mk_ite(negative, one, ones_term);
            }
            if c == BigInt::from(1u8) {
                return lhs;
            }
        }
        let sort = self.get(lhs).map_or(self.sorts.bool_sort, |t| t.sort);
        self.intern(TermKind::BvSdiv(lhs, rhs), sort)
    }

    /// Create an unsigned bit vector remainder.
    ///
    /// Folds two literals, including the **total** remainder-by-zero case
    /// `(bvurem s (_ bv0 m))` = `s`.
    pub fn mk_bv_urem(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if let Some(width) = self.bv_binop_width(lhs, rhs)
            && let Some((lhs_value, rhs_value)) = self.bv_const_pair(lhs, rhs, width)
        {
            return self.mk_bitvec(bv_fold::bv_urem(&lhs_value, &rhs_value, width), width);
        }
        // Constant-divisor identities (Z3 `mk_bv_urem_core`):
        // `x urem 0 = x`, `x urem 1 = 0`, `x urem 2^k = x & (2^k - 1)`.
        if let Some(width) = self.bv_binop_width(lhs, rhs)
            && let Some(c) = self.bv_const_unsigned(rhs, width)
        {
            if c == BigInt::ZERO {
                return lhs;
            }
            if c == BigInt::from(1u8) {
                return self.mk_bitvec(0, width);
            }
            if let Some(shift) = Self::power_of_two_exponent(&c, width) {
                let mask = BigInt::from(1u8) << shift as usize;
                let mask = mask - BigInt::from(1u8);
                let mask_term = self.mk_bitvec(mask, width);
                return self.mk_bv_and(lhs, mask_term);
            }
        }
        let sort = self.get(lhs).map_or(self.sorts.bool_sort, |t| t.sort);
        self.intern(TermKind::BvUrem(lhs, rhs), sort)
    }

    /// Create a signed bit vector remainder.
    ///
    /// Folds two literals, including the **total** remainder-by-zero case
    /// `(bvsrem s (_ bv0 m))` = `s`; for a symbolic dividend the divisor
    /// identities of Z3's `mk_bv_srem_core` fire: `x srem 1 = 0`,
    /// `x srem 0 = x`.
    pub fn mk_bv_srem(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if let Some(width) = self.bv_binop_width(lhs, rhs)
            && let Some((lhs_value, rhs_value)) = self.bv_const_pair(lhs, rhs, width)
        {
            return self.mk_bitvec(bv_fold::bv_srem(&lhs_value, &rhs_value, width), width);
        }
        if let Some(width) = self.bv_binop_width(lhs, rhs)
            && let Some(c) = self.bv_const_unsigned(rhs, width)
        {
            if c == BigInt::ZERO {
                return lhs;
            }
            if c == BigInt::from(1u8) {
                return self.mk_bitvec(0, width);
            }
        }
        let sort = self.get(lhs).map_or(self.sorts.bool_sort, |t| t.sort);
        self.intern(TermKind::BvSrem(lhs, rhs), sort)
    }

    /// Create a bit vector XOR.
    ///
    /// Folds two literals and applies `t ^ t -> 0` and `t ^ 0 -> t`.
    pub fn mk_bv_xor(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let (lhs, rhs) = canonical_pair(lhs, rhs);
        if let Some(width) = self.bv_binop_width(lhs, rhs) {
            let (lhs_value, rhs_value) = self.bv_operand_consts(lhs, rhs, width);
            if let (Some(lhs_value), Some(rhs_value)) = (&lhs_value, &rhs_value) {
                return self.mk_bitvec(bv_fold::bv_xor(lhs_value, rhs_value, width), width);
            }
            if lhs == rhs {
                return self.mk_bitvec(0i64, width);
            }
            if lhs_value.is_some_and(|value| value == BigInt::ZERO) {
                return rhs;
            }
            if rhs_value.is_some_and(|value| value == BigInt::ZERO) {
                return lhs;
            }
        }

        let sort = self.get(lhs).map(|t| t.sort);
        let sort = sort.unwrap_or_else(|| self.sorts.bitvec(32));
        self.intern(TermKind::BvXor(lhs, rhs), sort)
    }

    /// Create a bit vector shift left.
    ///
    /// Folds two literals; a shift distance of at least the width discards
    /// every bit, so `t << k` is `0` for any `t` once `k >= width`.
    /// Whether constant-distance shifts rewire to concat/extract at term
    /// construction (`NIXIE_BV_SHIFT_WIRING=1` enables; default off).
    ///
    /// The wiring is Z3 `mk_bv_shl`/`mk_bv_lshr`'s numeral case and is the
    /// piece that makes shift-heavy identities (`maxandminor*`, `bitrev*`)
    /// converge *syntactically* under the simplify cascade: the concat
    /// splices align piecewise instead of hiding inside a shift node.
    /// Gated because the concat-spine term shapes change the blast for
    /// every const-shift in the corpus (the reverted structural-rewriting
    /// study's rules belonged to this family and measured zero cells then —
    /// re-measured now that the NOT-descent cascade composes with them).
    fn shift_wiring_enabled() -> bool {
        #[cfg(feature = "std")]
        {
            use std::sync::OnceLock;
            static FLAG: OnceLock<bool> = OnceLock::new();
            // Default **on** (2026-09-12): the 509-file matched-null A/B
            // measured 287 vs 286 with zero verdict flips, and the serial
            // gains are deterministic — `mcm/54` 6.1× (43.5 → 7.1 s,
            // crossing the cap), bitrev 1.5–2× at every width — with RWS
            // verdicts identical across the family and the boundary movers
            // measured as load noise (vlsat3_g00 21.0 vs 21.5 s,
            // VS3-A7 15.8 vs 15.8 s serially).
            *FLAG.get_or_init(|| {
                !matches!(std::env::var("NIXIE_BV_SHIFT_WIRING"), Ok(v) if v == "0" || v.is_empty())
            })
        }
        #[cfg(not(feature = "std"))]
        {
            true
        }
    }

    /// Create a bit vector shift left.
    ///
    /// Folds two literals; a zero distance is the identity; and, under
    /// (the `NIXIE_BV_SHIFT_WIRING` gate), a constant distance `0 < k < w`
    /// rewires to `concat(x[w-1-k:0], 0^k)` (Z3 `mk_bv_shl`'s numeral
    /// case — the syntactic convergence piece for shift-heavy identities).
    pub fn mk_bv_shl(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if let Some(width) = self.bv_binop_width(lhs, rhs) {
            match self.fold_bv_shift(lhs, rhs, width, bv_fold::bv_shl) {
                ShiftFold::Value(value) => return self.mk_bitvec(value, width),
                ShiftFold::Identity => return lhs,
                ShiftFold::None => {}
            }
            // Constant-distance shift → concat/extract wiring (Z3
            // `mk_bv_shl`'s numeral case): `x << k =
            // concat(x[w-1-k:0], 0^k)` for `0 < k < w`, gated by
            // `NIXIE_BV_SHIFT_WIRING=1` (default off — the wiring is what
            // makes shift-heavy identities converge *syntactically* under
            // the simplify cascade, at the price of concat-spine terms).
            if Self::shift_wiring_enabled()
                && let Some(k) = self.bv_const_unsigned(rhs, width)
                && k > BigInt::ZERO
                && k < BigInt::from(u64::from(width))
            {
                let k = k.to_u64().unwrap_or(0) as u32;
                let low = self.mk_bv_extract(width - k - 1, 0, lhs);
                let zeros = self.mk_bitvec(BigInt::ZERO, k);
                return self.mk_bv_concat(low, zeros);
            }
        }

        let sort = self.get(lhs).map(|t| t.sort);
        let sort = sort.unwrap_or_else(|| self.sorts.bitvec(32));
        self.intern(TermKind::BvShl(lhs, rhs), sort)
    }

    /// Create a bit vector logical shift right.
    ///
    /// Folds two literals; a shift distance of at least the width discards
    /// every bit, so `t >>u k` is `0` for any `t` once `k >= width`.
    pub fn mk_bv_lshr(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if let Some(width) = self.bv_binop_width(lhs, rhs) {
            match self.fold_bv_shift(lhs, rhs, width, bv_fold::bv_lshr) {
                ShiftFold::Value(value) => return self.mk_bitvec(value, width),
                ShiftFold::Identity => return lhs,
                ShiftFold::None => {}
            }
            // Constant-distance shift → concat/extract wiring (Z3
            // `mk_bv_lshr`'s numeral case): `x >>u k =
            // concat(0^k, x[w-1:k])` for `0 < k < w`, gated with the
            // `mk_bv_shl` wiring (`NIXIE_BV_SHIFT_WIRING`).
            if Self::shift_wiring_enabled()
                && let Some(k) = self.bv_const_unsigned(rhs, width)
                && k > BigInt::ZERO
                && k < BigInt::from(u64::from(width))
            {
                let k = k.to_u64().unwrap_or(0) as u32;
                let zeros = self.mk_bitvec(BigInt::ZERO, k);
                let high = self.mk_bv_extract(width - 1, k, lhs);
                return self.mk_bv_concat(zeros, high);
            }
        }

        let sort = self.get(lhs).map(|t| t.sort);
        let sort = sort.unwrap_or_else(|| self.sorts.bitvec(32));
        self.intern(TermKind::BvLshr(lhs, rhs), sort)
    }

    /// Create a bit vector arithmetic shift right.
    ///
    /// Folds two literals.  Unlike the other two shifts, an over-wide
    /// distance does *not* fold on its own: `t >>s k` for `k >= width` is
    /// all-ones or zero depending on `t`'s sign bit, so it is only decidable
    /// when `t` is also literal.
    pub fn mk_bv_ashr(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if let Some(width) = self.bv_binop_width(lhs, rhs) {
            if let Some((lhs_value, rhs_value)) = self.bv_const_pair(lhs, rhs, width) {
                let folded = bv_fold::bv_ashr(&lhs_value, &rhs_value, width);
                return self.mk_bitvec(folded, width);
            }
            // t >>s 0 -> t.
            if self
                .bv_const_unsigned(rhs, width)
                .is_some_and(|amount| amount == BigInt::ZERO)
            {
                return lhs;
            }
        }

        let sort = self.get(lhs).map(|t| t.sort);
        let sort = sort.unwrap_or_else(|| self.sorts.bitvec(32));
        self.intern(TermKind::BvAshr(lhs, rhs), sort)
    }

    /// Shared folding for `bvshl` and `bvlshr`, whose results agree on the
    /// two operand-independent cases: shifting by `0` is the identity, and
    /// shifting by at least the width yields `0` regardless of the value.
    ///
    /// `fold_const` is the matching evaluator from
    /// [`super::bv_fold`] – an ordinary Rust function pointer chosen at the
    /// call site, not any form of dynamic evaluation.
    fn fold_bv_shift(
        &self,
        lhs: TermId,
        rhs: TermId,
        width: u32,
        fold_const: fn(&BigInt, &BigInt, u32) -> BigInt,
    ) -> ShiftFold {
        let Some(amount) = self.bv_const_unsigned(rhs, width) else {
            return ShiftFold::None;
        };
        if let Some(value) = self.bv_const_unsigned(lhs, width) {
            return ShiftFold::Value(fold_const(&value, &amount, width));
        }
        if amount == BigInt::ZERO {
            return ShiftFold::Identity;
        }
        if amount >= BigInt::from(width) {
            return ShiftFold::Value(BigInt::ZERO);
        }
        ShiftFold::None
    }
}

/// Outcome of folding a `bvshl` / `bvlshr` whose shift distance is literal.
enum ShiftFold {
    /// The whole shift evaluates to this literal value.
    Value(BigInt),
    /// The shift is the identity on its left operand (a zero distance).
    Identity,
    /// Nothing can be decided syntactically.
    None,
}

#[cfg(test)]
mod arith_folding_tests {
    use super::*;
    use num_traits::Zero;

    fn int_const_value(t: TermId, m: &TermManager) -> Option<BigInt> {
        match &m.get(t)?.kind {
            TermKind::IntConst(v) => Some(v.clone()),
            _ => None,
        }
    }

    fn real_const_value(t: TermId, m: &TermManager) -> Option<Rational64> {
        match &m.get(t)?.kind {
            TermKind::RealConst(v) => Some(*v),
            _ => None,
        }
    }

    /// The exact wide-literal sum that used to panic inside `num-rational`
    /// when the solver's `Ratio<i64>` accumulator folded it at parse time
    /// (and to *silently wrap* in release): `i64::MAX + 1` folds to the
    /// exact `2^63` `BigInt` constant at construction.
    #[test]
    fn wide_addition_folds_exactly_in_bigint() {
        let mut m = TermManager::new();
        let max = m.mk_int(i64::MAX);
        let one = m.mk_int(1);
        let sum = m.mk_add([max, one]);
        assert_eq!(int_const_value(sum, &m), Some(BigInt::from(2u32).pow(63)));
        // ...and a wide literal that only fits together as 2^64.
        let wide = m.mk_int(BigInt::from(2u32).pow(64) - 1);
        assert_eq!(
            int_const_value(m.mk_add([wide, one]), &m),
            Some(BigInt::from(2u32).pow(64))
        );
    }

    #[test]
    fn partial_add_folding_collects_numerals_at_the_end() {
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let x = m.mk_var("x", int_sort);
        let one = m.mk_int(1);
        let two = m.mk_int(2);
        // (+ x 1 2) -> (+ x 3)
        let t = m.mk_add([x, one, two]);
        match &m.get(t).expect("term").kind {
            TermKind::Add(args) => {
                assert_eq!(args.len(), 2);
                assert_eq!(args[0], x);
                assert_eq!(int_const_value(args[1], &m), Some(BigInt::from(3)));
            }
            other => panic!("expected Add, got {other:?}"),
        }
        // (+ x 1 -1) -> x
        let neg_one = m.mk_int(-1);
        assert_eq!(m.mk_add([x, one, neg_one]), x);
        // (+ 1 -1) -> 0
        let zero_sum = m.mk_add([one, neg_one]);
        assert_eq!(int_const_value(zero_sum, &m), Some(BigInt::zero()));
    }

    #[test]
    fn sub_neg_mul_fold_on_uniform_numerals() {
        let mut m = TermManager::new();
        let five = m.mk_int(5);
        let two = m.mk_int(2);
        assert_eq!(
            int_const_value(m.mk_sub(five, two), &m),
            Some(BigInt::from(3))
        );
        // i64::MIN negation is exact in BigInt.
        let min = m.mk_int(i64::MIN);
        let negated = m.mk_neg(min);
        assert_eq!(int_const_value(negated, &m), Some(-BigInt::from(i64::MIN)));
        // A product past i64 width folds exactly, and with no surviving
        // factors collapses to the numeral itself.
        let f1 = m.mk_int(1i64 << 40);
        let f2 = m.mk_int(1i64 << 40);
        let big = m.mk_mul([f1, f2]);
        assert_eq!(int_const_value(big, &m), Some(BigInt::from(2u32).pow(80)));
        // (* x 1) -> x, (* x 0) -> 0
        let int_sort = m.sorts.int_sort;
        let x = m.mk_var("x", int_sort);
        let one = m.mk_int(1);
        let zero = m.mk_int(0);
        assert_eq!(m.mk_mul([x, one]), x);
        assert_eq!(
            int_const_value(m.mk_mul([x, zero]), &m),
            Some(BigInt::zero())
        );
    }

    /// Euclidean `div`/`mod` fold exactly, on every sign combination, and a
    /// zero divisor never folds (SMT-LIB: uninterpreted).
    #[test]
    fn div_mod_fold_euclidean_and_never_on_zero() {
        let mut m = TermManager::new();
        for (a, b, q, r) in [
            (7i64, 2i64, 3i64, 1i64), // 7 = 2*3 + 1
            (7, -2, -3, 1),           // 7 = (-2)(-3) + 1
            (-7, 2, -4, 1),           // -7 = 2*(-4) + 1
            (-7, -2, 4, 1),           // -7 = (-2)*4 + 1
        ] {
            let ma = m.mk_int(a);
            let mb = m.mk_int(b);
            assert_eq!(
                int_const_value(m.mk_div(ma, mb), &m),
                Some(BigInt::from(q)),
                "div {a} {b}"
            );
            assert_eq!(
                int_const_value(m.mk_mod(ma, mb), &m),
                Some(BigInt::from(r)),
                "mod {a} {b}"
            );
        }
        // The i64-overflow corner: Euclidean (div i64::MIN -1) = 2^63 with
        // remainder 0 -- exact in `BigInt`, where an i64 path would overflow.
        let min = m.mk_int(i64::MIN);
        let neg_one = m.mk_int(-1);
        assert_eq!(
            int_const_value(m.mk_div(min, neg_one), &m),
            Some(BigInt::from(2u32).pow(63))
        );
        assert_eq!(
            int_const_value(m.mk_mod(min, neg_one), &m),
            Some(BigInt::zero())
        );
        // Zero divisor: the term must survive as a Div/Mod node.
        let five = m.mk_int(5);
        let zero = m.mk_int(0);
        let dz = m.mk_div(five, zero);
        assert!(matches!(
            &m.get(dz).expect("term").kind,
            TermKind::Div(_, _)
        ));
        let mz = m.mk_mod(five, zero);
        assert!(matches!(
            &m.get(mz).expect("term").kind,
            TermKind::Mod(_, _)
        ));
    }

    /// Real folding is exact where representable and refused (not approximated)
    /// where not.
    #[test]
    fn real_folding_is_exact_or_refused() {
        let mut m = TermManager::new();
        let half = m.mk_real(Rational64::new(1, 2));
        // (+ 0.5 0.5) -> 1.0
        let sum = m.mk_add([half, half]);
        assert_eq!(real_const_value(sum, &m), Some(Rational64::from_integer(1)));
        // (/ 1.0 4.0) -> 0.25
        let one = m.mk_real(Rational64::from_integer(1));
        let four = m.mk_real(Rational64::from_integer(4));
        assert_eq!(
            real_const_value(m.mk_div(one, four), &m),
            Some(Rational64::new(1, 4))
        );
        // A zero real product collapses to the REAL zero (sort preserved).
        let x_real = m.mk_var("xr", m.sorts.real_sort);
        let r_zero = m.mk_real(Rational64::zero());
        let prod = m.mk_mul([x_real, r_zero]);
        assert!(matches!(
            &m.get(prod).expect("term").kind,
            TermKind::RealConst(r) if r.is_zero()
        ));
    }
}
