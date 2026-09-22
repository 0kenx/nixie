//! Term representation

use crate::interner::Spur;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::sort::SortId;
use num_bigint::BigInt;
use num_rational::Rational64;
use smallvec::SmallVec;

/// IEEE 754 rounding modes for floating-point operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[allow(clippy::upper_case_acronyms)]
pub enum RoundingMode {
    /// Round to nearest, ties to even
    RNE,
    /// Round to nearest, ties away from zero
    RNA,
    /// Round toward positive infinity
    RTP,
    /// Round toward negative infinity
    RTN,
    /// Round toward zero
    RTZ,
}

impl RoundingMode {
    /// All five rounding modes, in canonical (SMT-LIB) order.
    ///
    /// The order is load-bearing: the symbolic-mode case split in the parser
    /// (`expand_symbolic_rm`) builds its nested `ite` over this array, with the
    /// LAST mode as the unguarded `else` branch, so the array's order is the
    /// split's branch order. (Ported from upstream v0.3.3.)
    pub const ALL: [RoundingMode; 5] = [
        RoundingMode::RNE,
        RoundingMode::RNA,
        RoundingMode::RTP,
        RoundingMode::RTN,
        RoundingMode::RTZ,
    ];
}

/// Unique identifier for a term in the arena
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TermId(pub u32);

impl TermId {
    /// Create a new TermId from a raw value
    #[must_use]
    pub const fn new(id: u32) -> Self {
        Self(id)
    }

    /// Get the raw ID value
    #[must_use]
    pub const fn raw(self) -> u32 {
        self.0
    }
}

impl From<u32> for TermId {
    fn from(id: u32) -> Self {
        Self(id)
    }
}

/// The kind of a term
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TermKind {
    // Constants
    /// Boolean true
    True,
    /// Boolean false
    False,
    /// Integer constant
    IntConst(BigInt),
    /// Rational constant
    RealConst(Rational64),
    /// Bit vector constant (value, width)
    BitVecConst {
        /// Value of the bit vector
        value: BigInt,
        /// Width in bits
        width: u32,
    },

    // Variables
    /// Named variable
    Var(Spur),

    // Boolean operations
    /// Logical NOT
    Not(TermId),
    /// Logical AND
    And(SmallVec<[TermId; 4]>),
    /// Logical OR
    Or(SmallVec<[TermId; 4]>),
    /// Logical XOR
    Xor(TermId, TermId),
    /// Logical implication
    Implies(TermId, TermId),
    /// If-then-else
    Ite(TermId, TermId, TermId),

    // Equality and comparison
    /// Equality
    Eq(TermId, TermId),
    /// Distinct (all different)
    Distinct(SmallVec<[TermId; 4]>),

    // Arithmetic operations
    /// Negation
    Neg(TermId),
    /// Addition
    Add(SmallVec<[TermId; 4]>),
    /// Subtraction
    Sub(TermId, TermId),
    /// Multiplication
    Mul(SmallVec<[TermId; 4]>),
    /// Integer division
    Div(TermId, TermId),
    /// Modulo
    Mod(TermId, TermId),
    /// Less than
    Lt(TermId, TermId),
    /// Less than or equal
    Le(TermId, TermId),
    /// Greater than
    Gt(TermId, TermId),
    /// Greater than or equal
    Ge(TermId, TermId),

    // Transcendental functions over the reals (`Real -> Real`).  These make
    // the constraint language undecidable; the transcendental theory answers
    // them with dReal-style delta-satisfiability (interval constraint
    // propagation — `nixie-theories/src/trans/`, `docs/TRANS.md`), never by
    // pretending they are linear.
    /// `e^x`
    Exp(TermId),
    /// Natural logarithm.  Total semantics: `log(x)` for `x ≤ 0` is `−∞`.
    Log(TermId),
    /// `sin(x)`
    Sin(TermId),
    /// `cos(x)`
    Cos(TermId),
    /// `atan(x)`, values in `(−π/2, π/2)`
    Atan(TermId),
    /// Square root.  Total semantics: `sqrt(x)` for `x < 0` is `0`.
    Sqrt(TermId),

    // BitVector operations
    /// Bit vector concatenation
    BvConcat(TermId, TermId),
    /// Bit vector extraction (high, low, arg)
    BvExtract {
        /// High bit index
        high: u32,
        /// Low bit index
        low: u32,
        /// Term to extract from
        arg: TermId,
    },
    /// Bit vector NOT
    BvNot(TermId),
    /// Bit vector AND
    BvAnd(TermId, TermId),
    /// Bit vector OR
    BvOr(TermId, TermId),
    /// Bit vector XOR
    BvXor(TermId, TermId),
    /// Bit vector addition
    BvAdd(TermId, TermId),
    /// Bit vector subtraction
    BvSub(TermId, TermId),
    /// Bit vector multiplication
    BvMul(TermId, TermId),
    /// Bit vector unsigned division
    BvUdiv(TermId, TermId),
    /// Bit vector signed division
    BvSdiv(TermId, TermId),
    /// Bit vector unsigned remainder
    BvUrem(TermId, TermId),
    /// Bit vector signed remainder
    BvSrem(TermId, TermId),
    /// Bit vector shift left
    BvShl(TermId, TermId),
    /// Bit vector logical shift right
    BvLshr(TermId, TermId),
    /// Bit vector arithmetic shift right
    BvAshr(TermId, TermId),
    /// Bit vector unsigned less than
    BvUlt(TermId, TermId),
    /// Bit vector unsigned less than or equal
    BvUle(TermId, TermId),
    /// Bit vector signed less than
    BvSlt(TermId, TermId),
    /// Bit vector signed less than or equal
    BvSle(TermId, TermId),

    // Array operations
    /// Array select
    Select(TermId, TermId),
    /// Array store
    Store(TermId, TermId, TermId),

    // String operations
    /// String literal
    StringLit(String),
    /// String concatenation
    StrConcat(TermId, TermId),
    /// String length
    StrLen(TermId),
    /// Substring (string, start, length)
    StrSubstr(TermId, TermId, TermId),
    /// Character at index
    StrAt(TermId, TermId),
    /// Contains substring
    StrContains(TermId, TermId),
    /// Prefix of
    StrPrefixOf(TermId, TermId),
    /// Suffix of
    StrSuffixOf(TermId, TermId),
    /// Index of (string, substring, offset)
    StrIndexOf(TermId, TermId, TermId),
    /// Replace (string, pattern, replacement)
    StrReplace(TermId, TermId, TermId),
    /// Replace all (string, pattern, replacement)
    StrReplaceAll(TermId, TermId, TermId),
    /// Replace the leftmost shortest regular-language match
    /// (`str.replace_re`: string, regex, replacement)
    StrReplaceRe(TermId, TermId, TermId),
    /// Replace every shortest non-empty regular-language match
    /// (`str.replace_re_all`: string, regex, replacement)
    StrReplaceReAll(TermId, TermId, TermId),
    /// String to integer conversion
    StrToInt(TermId),
    /// Integer to string conversion
    IntToStr(TermId),
    /// String in regular expression
    StrInRe(TermId, TermId),
    /// Strict lexicographic order over code points (`str.<`)
    StrLt(TermId, TermId),
    /// Reflexive lexicographic order over code points (`str.<=`)
    StrLe(TermId, TermId),
    /// Code point of a one-character string, `-1` otherwise (`str.to_code`)
    StrToCode(TermId),
    /// One-character string for a code point, `""` outside the alphabet
    /// (`str.from_code`)
    StrFromCode(TermId),

    // Floating-point operations
    /// Floating-point numeral (sign_bit, exponent_bitvec, significand_bitvec)
    /// Represented as three bitvectors
    FpLit {
        /// Sign bit (1 bit)
        sign: bool,
        /// Exponent bitvector
        exp: BigInt,
        /// Significand bitvector
        sig: BigInt,
        /// Exponent width
        eb: u32,
        /// Significand width
        sb: u32,
    },
    /// Floating-point positive infinity
    FpPlusInfinity {
        /// Exponent width
        eb: u32,
        /// Significand width
        sb: u32,
    },
    /// Floating-point negative infinity
    FpMinusInfinity {
        /// Exponent width
        eb: u32,
        /// Significand width
        sb: u32,
    },
    /// Floating-point positive zero
    FpPlusZero {
        /// Exponent width
        eb: u32,
        /// Significand width
        sb: u32,
    },
    /// Floating-point negative zero
    FpMinusZero {
        /// Exponent width
        eb: u32,
        /// Significand width
        sb: u32,
    },
    /// Floating-point NaN
    FpNaN {
        /// Exponent width
        eb: u32,
        /// Significand width
        sb: u32,
    },

    // FP unary operations
    /// Floating-point absolute value
    FpAbs(TermId),
    /// Floating-point negation
    FpNeg(TermId),
    /// Floating-point square root (rounding mode, arg)
    FpSqrt(RoundingMode, TermId),
    /// Round to integral (rounding mode, arg)
    FpRoundToIntegral(RoundingMode, TermId),

    // FP binary operations
    /// Floating-point addition (rounding mode, lhs, rhs)
    FpAdd(RoundingMode, TermId, TermId),
    /// Floating-point subtraction (rounding mode, lhs, rhs)
    FpSub(RoundingMode, TermId, TermId),
    /// Floating-point multiplication (rounding mode, lhs, rhs)
    FpMul(RoundingMode, TermId, TermId),
    /// Floating-point division (rounding mode, lhs, rhs)
    FpDiv(RoundingMode, TermId, TermId),
    /// Floating-point remainder (lhs, rhs)
    FpRem(TermId, TermId),
    /// Floating-point minimum
    FpMin(TermId, TermId),
    /// Floating-point maximum
    FpMax(TermId, TermId),
    /// Floating-point less than or equal
    FpLeq(TermId, TermId),
    /// Floating-point less than
    FpLt(TermId, TermId),
    /// Floating-point greater than or equal
    FpGeq(TermId, TermId),
    /// Floating-point greater than
    FpGt(TermId, TermId),
    /// Floating-point equality
    FpEq(TermId, TermId),

    // FP ternary operations
    /// Fused multiply-add: (x * y) + z (rounding mode, x, y, z)
    FpFma(RoundingMode, TermId, TermId, TermId),

    // FP predicates
    /// Check if normal floating-point number
    FpIsNormal(TermId),
    /// Check if subnormal floating-point number
    FpIsSubnormal(TermId),
    /// Check if zero
    FpIsZero(TermId),
    /// Check if infinite
    FpIsInfinite(TermId),
    /// Check if NaN
    FpIsNaN(TermId),
    /// Check if negative
    FpIsNegative(TermId),
    /// Check if positive
    FpIsPositive(TermId),

    // FP conversions
    /// Convert to floating-point from another FP format (rm, arg, target_eb, target_sb)
    FpToFp {
        /// Rounding mode
        rm: RoundingMode,
        /// Term to convert
        arg: TermId,
        /// Target exponent width
        eb: u32,
        /// Target significand width
        sb: u32,
    },
    /// Convert floating-point to signed bitvector (rm, arg, width)
    FpToSBV {
        /// Rounding mode
        rm: RoundingMode,
        /// Term to convert
        arg: TermId,
        /// Target bitvector width
        width: u32,
    },
    /// Convert floating-point to unsigned bitvector (rm, arg, width)
    FpToUBV {
        /// Rounding mode
        rm: RoundingMode,
        /// Term to convert
        arg: TermId,
        /// Target bitvector width
        width: u32,
    },
    /// Convert floating-point to real
    FpToReal(TermId),
    /// Convert real to floating-point (rm, arg, eb, sb)
    RealToFp {
        /// Rounding mode
        rm: RoundingMode,
        /// Term to convert
        arg: TermId,
        /// Exponent width
        eb: u32,
        /// Significand width
        sb: u32,
    },
    /// Convert signed bitvector to floating-point (rm, arg, eb, sb)
    SBVToFp {
        /// Rounding mode
        rm: RoundingMode,
        /// Term to convert
        arg: TermId,
        /// Exponent width
        eb: u32,
        /// Significand width
        sb: u32,
    },
    /// Convert unsigned bitvector to floating-point (rm, arg, eb, sb)
    UBVToFp {
        /// Rounding mode
        rm: RoundingMode,
        /// Term to convert
        arg: TermId,
        /// Exponent width
        eb: u32,
        /// Significand width
        sb: u32,
    },

    // Finite-field operations (SMT-LIB `QF_FF`, the [OKTB23] signature:
    // four operators, one predicate). Values are normalized into `[0, p)` at
    // construction, which is load-bearing for hash-consing: `#f8m7` and
    // `#f1m7` must be the same `TermId` or the rewriter's constant folding
    // and the encoder's polynomial construction disagree about when two
    // literals are equal.
    /// Finite-field numeral, normalized into `[0, p)`.
    FfConst {
        /// The field element's value in `[0, p)`.
        value: BigInt,
        /// The field it lives in.
        field: crate::sort::field::FieldId,
    },
    /// Field addition, n-ary ≥ 2 (single operands are collapsed by the
    /// builder's normal form).
    FfAdd(SmallVec<[TermId; 4]>),
    /// Field multiplication, n-ary ≥ 2.
    FfMul(SmallVec<[TermId; 4]>),
    /// Field negation. The normal form rewrites this to `(-1)·t`, so this
    /// variant exists for API-built terms before simplification.
    FfNeg(TermId),
    /// Little-endian bit-sum: `Σ 2ⁱ · bᵢ` over field-element operands.
    FfBitsum(SmallVec<[TermId; 4]>),

    // Uninterpreted functions
    /// Function application
    Apply {
        /// Function symbol
        func: Spur,
        /// Arguments
        args: SmallVec<[TermId; 4]>,
    },

    // Algebraic datatypes
    /// Datatype constructor application
    DtConstructor {
        /// Constructor name (e.g., "cons", "nil")
        constructor: Spur,
        /// Arguments to the constructor
        args: SmallVec<[TermId; 4]>,
    },
    /// Datatype tester/discriminator (checks if term was built with a specific constructor)
    DtTester {
        /// Constructor name to test for (e.g., "is-cons")
        constructor: Spur,
        /// Term to test
        arg: TermId,
    },
    /// Datatype selector/accessor (extracts a field from a constructor)
    DtSelector {
        /// Selector name (e.g., "head", "tail")
        selector: Spur,
        /// Term to extract from
        arg: TermId,
    },

    // Quantifiers
    /// Universal quantification
    Forall {
        /// Bound variables (name, sort)
        vars: SmallVec<[(Spur, SortId); 2]>,
        /// Body
        body: TermId,
        /// Instantiation patterns (triggers)
        /// Each pattern is a list of terms that guide instantiation
        patterns: SmallVec<[SmallVec<[TermId; 2]>; 2]>,
    },
    /// Existential quantification
    Exists {
        /// Bound variables (name, sort)
        vars: SmallVec<[(Spur, SortId); 2]>,
        /// Body
        body: TermId,
        /// Instantiation patterns (triggers)
        /// Each pattern is a list of terms that guide instantiation
        patterns: SmallVec<[SmallVec<[TermId; 2]>; 2]>,
    },

    // Let bindings
    /// Let expression
    Let {
        /// Bindings (name, value)
        bindings: SmallVec<[(Spur, TermId); 2]>,
        /// Body
        body: TermId,
    },

    // Match expressions
    /// Pattern matching on algebraic datatypes
    Match {
        /// The term being matched (scrutinee)
        scrutinee: TermId,
        /// The match cases (patterns and bodies)
        cases: SmallVec<[MatchCase; 4]>,
    },

    // Finite-set operations (SMT-LIB theory of finite sets, as CVC5
    // implements it in `src/theory/sets`). Deliberately *not* modelled as
    // `Array(elem, Bool)`: an array has no union, no intersection and no
    // cardinality, so every set operation would need a quantifier or a
    // pointwise expansion over a candidate list.
    /// The empty set at a given element sort: `(as set.empty (Set T))`.
    ///
    /// Carries its **set** sort, because the empty set is not sort-inferable
    /// from its (absent) elements.
    SetEmpty(SortId),
    /// `(set.singleton x)` — the one-element set containing `x`.
    SetSingleton(TermId),
    /// `(set.union a b)`.
    SetUnion(TermId, TermId),
    /// `(set.inter a b)`.
    SetInter(TermId, TermId),
    /// `(set.minus a b)` — set difference.
    SetMinus(TermId, TermId),
    /// `(set.member x s)` — a `Bool`.
    SetMember(TermId, TermId),
    /// `(set.subset a b)` — a `Bool`.
    SetSubset(TermId, TermId),
    /// `(set.card s)` — an `Int`.
    ///
    /// Kept as its own kind rather than expanded: cardinality is what forces
    /// set reasoning to interact with arithmetic, and CVC5 gives it a whole
    /// module (`cardinality_extension.cpp`) for that reason.
    SetCard(TermId),
    /// `(set.complement s)` — the complement relative to the element sort's
    /// universe.
    ///
    /// Membership is decidable pointwise (`x ∈ ~s ↔ x ∉ s`); cardinality is
    /// only meaningful when the universe is finite, which the reduction
    /// checks before emitting any arithmetic.
    SetComplement(TermId),
    /// `(as set.universe (Set T))` — the universe set of an element sort.
    ///
    /// Carries its **set** sort, like [`TermKind::SetEmpty`].
    SetUniv(SortId),
    /// `(set.choose s)` — some element of `s`, as CVC5's `SET_CHOOSE`:
    /// `choose(s) ∈ s ↔ s ≠ ∅`, and `s = t → choose(s) = choose(t)` by
    /// congruence.
    SetChoose(TermId),
    /// `(rel.join r s)` — relation composition (CVC5 `RELATION_JOIN`).
    ///
    /// Both operands are relations (sets of tuples) whose boundary sorts
    /// agree; the result relates `r`'s front to `s`'s back through the
    /// shared middle: `(a, b) ∈ r ⨝ s  ⇔  ∃x. (a, x) ∈ r ∧ (x, b) ∈ s`.
    /// The eager reduction skolemizes `x` per (element, join-term), exactly
    /// like the disequality witnesses.
    SetRelJoin(TermId, TermId),
    /// `(rel.product r s)` — cartesian product (CVC5 `RELATION_PRODUCT`).
    ///
    /// Operands are sets (of tuples or plain); the result pairs them:
    /// `(t, u) ∈ r × s  ⇔  t ∈ r ∧ u ∈ s`.
    SetRelProduct(TermId, TermId),
    /// `(rel.transpose r)` — the converse relation (CVC5
    /// `RELATION_TRANSPOSE`): `t ∈ ~r  ⇔  rev(t) ∈ r`, with `rev` the
    /// component-reversed tuple.
    SetRelTranspose(TermId),
    /// `(rel.iden s)` — the identity relation *over* the set `s` (CVC5
    /// `RELATION_IDEN`): `(a, b) ∈ iden(s)  ⇔  a = b ∧ a ∈ s`. Note the
    /// operand is a plain set, not a relation.
    SetRelIden(TermId),
    /// The empty bag at a given element sort: `(as bag.empty (Bag T))`
    /// (CVC5 `BAG_EMPTY`).
    ///
    /// Carries its **bag** sort, because the empty bag is not
    /// sort-inferable from its (absent) elements — exactly like
    /// [`TermKind::SetEmpty`].
    BagEmpty(SortId),
    /// `(bag e n)` — the bag containing `n` copies of `e` (CVC5
    /// `BAG_MAKE`): `bag.count e (bag e n) = n`, zero for anything else.
    ///
    /// The bag theory's "singleton": every value is a finite union of
    /// these, exactly as every set value is a union of
    /// [`TermKind::SetSingleton`]s.
    BagMake(TermId, TermId),
    /// `(bag.union_max a b)` — bag union by maximum multiplicity (CVC5
    /// `BAG_UNION_MAX`): `count(x, a ∪ b) = max(count(x,a), count(x,b))`.
    BagUnionMax(TermId, TermId),
    /// `(bag.union_disjoint a b)` — bag union by sum (CVC5
    /// `BAG_UNION_DISJOINT`): `count(x, a ⊎ b) = count(x,a) + count(x,b)`.
    BagUnionDisjoint(TermId, TermId),
    /// `(bag.inter_min a b)` — bag intersection by minimum multiplicity
    /// (CVC5 `BAG_INTER_MIN`): `count(x, a ∩ b) = min(count(x,a),
    /// count(x,b))`.
    BagInterMin(TermId, TermId),
    /// `(bag.difference_subtract a b)` — bag difference by subtraction
    /// (CVC5 `BAG_DIFFERENCE_SUBTRACT`):
    /// `count(x, a \ b) = max(count(x,a) − count(x,b), 0)`.
    BagDifferenceSubtract(TermId, TermId),
    /// `(bag.difference_remove a b)` — bag difference by removal (CVC5
    /// `BAG_DIFFERENCE_REMOVE`): removes `x` entirely when `b` contains
    /// it at all — `count(x, a \\ b) = ite(count(x,b) > 0, 0,
    /// count(x,a))`.
    BagDifferenceRemove(TermId, TermId),
    /// `(bag.member x b)` — a `Bool` (CVC5 `BAG_MEMBER`):
    /// `x ∈ b ⇔ count(x, b) ≥ 1`.
    BagMember(TermId, TermId),
    /// `(bag.subbag a b)` — a `Bool` (CVC5 `BAG_SUBBAG`): bag inclusion,
    /// pointwise `count(x,a) ≤ count(x,b)`.
    BagSubbag(TermId, TermId),
    /// `(bag.count x b)` — an `Int` (CVC5 `BAG_COUNT`): the multiplicity
    /// of `x` in `b`.
    ///
    /// Kept as its own kind: it is the bag theory's analogue of
    /// [`TermKind::SetMember`] *and* of [`TermKind::SetCard`] at once —
    /// the reduction grounds every bag constraint into arithmetic over
    /// count terms, which is what makes the fragment decidable without
    /// enumerating multiplicities.
    BagCount(TermId, TermId),
    /// `(bag.card b)` — an `Int` (CVC5 `BAG_CARD`): the sum of the
    /// multiplicities.
    BagCard(TermId),
    /// `(bag.setof b)` — duplicate removal (CVC5 `BAG_SETOF`, the delta
    /// operator): `count(x, setof b) = ite(count(x,b) > 0, 1, 0)`.
    BagSetof(TermId),
    /// `(bag.choose b)` — some element of `b` (CVC5 `BAG_CHOOSE`):
    /// `b ≠ ∅ → count(choose(b), b) ≥ 1`, and `choose` is congruent
    /// (`a = b → choose(a) = choose(b)`); of an empty bag it is an
    /// unspecified value of the element sort. The result sort is the
    /// element sort.
    BagChoose(TermId),
    /// `(bag.map f b)` — pointwise image (CVC5 `BAG_MAP`):
    /// `count(y, map(f, b)) = Σ_x ite(f(x) = y, count(x, b), 0)` over the
    /// distinct-valued elements of the domain, and the cardinality is
    /// preserved exactly (`|map(f, b)| = |b|` — every copy maps to one
    /// copy). Carries the function's name symbol and its **codomain**
    /// sort (a bare symbol is not a term, so the image bag's element
    /// sort must be stored); the result sort is `(Bag ret)`.
    ///
    /// A `define-fun` function is inlined per element by the reduction
    /// (matching the parser's call-site substitution); a `declare-fun`
    /// symbol becomes an `Apply` the EUF layer owns.
    BagMap {
        /// The function's interned name.
        func: Spur,
        /// The function's codomain sort: the image bag's element sort.
        ret: SortId,
        /// The domain bag.
        bag: TermId,
    },
    /// `(bag.filter p b)` — the sub-bag of elements satisfying `p` (CVC5
    /// `BAG_FILTER`): `count(x, filter(p, b)) = ite(p(x), count(x, b), 0)`
    /// — exact per element (filter only removes), with `|filter(p, b)| ≤
    /// |b|`. Carries the predicate's name symbol; the result sort is the
    /// operand's own bag sort.
    BagFilter {
        /// The predicate's interned name.
        pred: Spur,
        /// The bag.
        bag: TermId,
    },
    /// `(bag.fold f t b)` — fold `f` over the elements of `b` with
    /// multiplicity, starting from `t` (CVC5 `BAG_FOLD`): the function has
    /// type `(-> T1 T2 T2)` and takes its **element first, accumulator
    /// second** (`combine_i = f(elements_i, combine_{i-1})`, exactly
    /// CVC5's `reduceFoldOperator` and `evaluateBagFold`), so
    /// `fold(f, t, (bag y n)) = f(y, f(y, … f(y, t) …))` with `n`
    /// applications. Carries the function's name symbol, the initial
    /// accumulator, and the domain bag; the result sort is `init`'s.
    ///
    /// The reduction unrolls a ground multiset (built from `∅`,
    /// `(bag y n)` with numeral `n`, `⊎` and bag-shaped `ite`) into that
    /// finite application chain, the way `bag.map` inlines its body per
    /// element. A fold is only *order-insensitive* when the combining
    /// function satisfies the exchange law `f(e1, f(e2, a)) =
    /// f(e2, f(e1, a))` (commutativity+associativity imply it); the
    /// reduction proves the law by simplification before unrolling a
    /// multiset with two or more distinct element spellings, and declines
    /// (`incomplete`) anything it cannot unroll — a free fold term with
    /// the honesty gate raised, never a guessed value.
    BagFold {
        /// The function's interned name (binary: element, accumulator).
        func: Spur,
        /// The initial accumulator value.
        init: TermId,
        /// The domain bag.
        bag: TermId,
    },
    /// Native generic sequence operator (including the typed empty value).
    Sequence(super::sequence::SeqOp, SmallVec<[TermId; 4]>),
}

/// A case in a match expression.
///
/// Each case consists of a pattern (constructor with optional bindings)
/// and a body expression to evaluate when the pattern matches.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MatchCase {
    /// The constructor to match, or None for a variable/wildcard pattern
    pub constructor: Option<Spur>,
    /// Variable bindings for constructor arguments
    pub bindings: SmallVec<[Spur; 4]>,
    /// The body expression to evaluate when matched
    pub body: TermId,
}

/// A term in the SMT-LIB2 sense
#[derive(Debug, Clone)]
pub struct Term {
    /// Unique identifier
    pub id: TermId,
    /// The kind of this term
    pub kind: TermKind,
    /// The sort of this term
    pub sort: SortId,
}

/// Instantiation pattern for quantifier triggers.
/// Each pattern is a list of terms that guide quantifier instantiation.
pub type InstPattern = SmallVec<[TermId; 2]>;

impl Term {
    /// Check if this term is a constant
    #[must_use]
    pub fn is_const(&self) -> bool {
        matches!(
            self.kind,
            TermKind::True
                | TermKind::False
                | TermKind::IntConst(_)
                | TermKind::RealConst(_)
                | TermKind::BitVecConst { .. }
                | TermKind::FfConst { .. }
        )
    }

    /// Check if this term is a variable
    #[must_use]
    pub fn is_var(&self) -> bool {
        matches!(self.kind, TermKind::Var(_))
    }

    /// Check if this term is a boolean constant
    #[must_use]
    pub fn as_bool(&self) -> Option<bool> {
        match self.kind {
            TermKind::True => Some(true),
            TermKind::False => Some(false),
            _ => None,
        }
    }
}
