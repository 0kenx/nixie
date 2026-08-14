//! The value domain and the candidate interpretation the certifier verifies.

use core::cmp::Ordering;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::interner::Spur;
use oxiz_core::sort::SortId;

#[allow(unused_imports)]
use crate::prelude::*;

/// A value of the sorts the certifier interprets: `Int`, `Real` and `Bool`.
///
/// Every other sort makes the goal ineligible (see
/// [`value_sort`]), so a `CertValue` is always a *concrete*
/// element of the domain – never a symbolic residue.  That is what lets the
/// certifier's verdict be a genuine model check rather than an approximation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum CertValue {
    /// An integer.
    Int(BigInt),
    /// A rational.
    Real(BigRational),
    /// A boolean.
    Bool(bool),
}

impl CertValue {
    /// The integer this value holds, or `None` for any other domain.
    pub(crate) fn as_int(&self) -> Option<&BigInt> {
        match self {
            CertValue::Int(n) => Some(n),
            CertValue::Real(_) | CertValue::Bool(_) => None,
        }
    }

    /// The rational this value holds, or `None` for any other domain.
    pub(crate) fn as_real(&self) -> Option<&BigRational> {
        match self {
            CertValue::Real(r) => Some(r),
            CertValue::Int(_) | CertValue::Bool(_) => None,
        }
    }

    /// The boolean this value holds, or `None` for any other domain.
    pub(crate) fn as_bool(&self) -> Option<bool> {
        match self {
            CertValue::Bool(b) => Some(*b),
            CertValue::Int(_) | CertValue::Real(_) => None,
        }
    }

    /// Order two integers, or `None` when either side is a boolean.
    pub(crate) fn compare_int(&self, other: &CertValue) -> Option<Ordering> {
        Some(self.as_int()?.cmp(other.as_int()?))
    }
}

/// The sorts the certifier can enumerate and evaluate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ValueSort {
    /// `Int`.
    Int,
    /// `Real`.
    Real,
    /// `Bool`.
    Bool,
}

/// Classify a sort, or `None` when the certifier cannot interpret it.
///
/// Declining here is what keeps the certifier honest on bit-vectors, arrays,
/// datatypes and uninterpreted sorts: those goals simply never certify and
/// keep their existing `unknown` answer.
///
/// `Int` and `Real` are classified but *never mixed*: the integer engine
/// ([`super::eval`]) declines a `Real` and the real engine
/// ([`super::real`]) declines an `Int`, so each verdict rests on the
/// completeness argument written for its own domain.
pub(crate) fn value_sort(sort: SortId, manager: &TermManager) -> Option<ValueSort> {
    if sort == manager.sorts.int_sort {
        Some(ValueSort::Int)
    } else if sort == manager.sorts.real_sort {
        Some(ValueSort::Real)
    } else if sort == manager.sorts.bool_sort {
        Some(ValueSort::Bool)
    } else {
        None
    }
}

/// Read a term that is already a literal (`3`, `true`, `false`) as a value.
///
/// Returns `None` for anything else – including a `Neg`/`Sub` that would fold
/// to a literal.  A caller uses this to decide whether a *model entry* is
/// concrete enough to become a pin, and a non-literal entry is simply skipped:
/// the candidate interpretation is verified afterwards regardless of where its
/// pins came from, so skipping one costs completeness only.
pub(crate) fn literal_value(term: TermId, manager: &TermManager) -> Option<CertValue> {
    match manager.get(term).map(|t| &t.kind) {
        Some(TermKind::IntConst(n)) => Some(CertValue::Int(n.clone())),
        Some(TermKind::RealConst(r)) => Some(CertValue::Real(rational_of(*r))),
        Some(TermKind::True) => Some(CertValue::Bool(true)),
        Some(TermKind::False) => Some(CertValue::Bool(false)),
        _ => None,
    }
}

/// Widen the AST's fixed-width rational to the arbitrary-precision one the
/// real certifier computes with.
///
/// The real engine adds midpoints and solves `a·x + b = 0` repeatedly, so its
/// intermediate denominators grow past what an `i64` numerator/denominator
/// pair can hold; widening at the boundary keeps every later step exact
/// instead of silently wrapping.
pub(crate) fn rational_of(value: num_rational::Rational64) -> BigRational {
    BigRational::new(BigInt::from(*value.numer()), BigInt::from(*value.denom()))
}

/// Read a term that denotes a *rational literal* – `2.5`, `3`, `(- 2.5)` – as
/// an exact rational, or `None` for anything else.
///
/// Unlike [`literal_value`] this folds a negation, because SMT-LIB writes a
/// negative literal as `(- 2.5)` and the resulting `Neg` node is still a
/// literal in every sense that matters here: its value is fixed by the term
/// alone, with no interpretation involved.  Deeper arithmetic is *not* folded –
/// a pin has to come from something the goal states outright.
pub(crate) fn rational_literal(term: TermId, manager: &TermManager) -> Option<BigRational> {
    // Iterative: `(- (- ... 2.5))` nests as deep as the input says, and a
    // native recursion here would trade a decline for a stack overflow.
    let mut current = term;
    let mut negated = false;
    loop {
        match manager.get(current).map(|t| &t.kind) {
            Some(TermKind::IntConst(n)) => {
                let value = BigRational::from(n.clone());
                return Some(if negated { -value } else { value });
            }
            Some(TermKind::RealConst(r)) => {
                let value = rational_of(*r);
                return Some(if negated { -value } else { value });
            }
            Some(TermKind::Neg(inner)) => {
                negated = !negated;
                current = *inner;
            }
            _ => return None,
        }
    }
}

/// Zero and one as arbitrary-precision rationals.
pub(crate) fn rat_zero() -> BigRational {
    BigRational::zero()
}

/// One as an arbitrary-precision rational.
pub(crate) fn rat_one() -> BigRational {
    BigRational::one()
}

/// The interpretation of one uninterpreted function: a finite graph of pinned
/// argument tuples plus a single value everywhere else.
///
/// This "pins + default" shape is precisely what makes the certifier's finite
/// check complete for the fragment it accepts: outside the pinned tuples the
/// function is *constant*, so two arguments that no atom can tell apart give
/// literally the same value.  See [`super`] for the region argument that turns
/// this into a proof.
#[derive(Clone, Debug)]
pub(crate) struct FuncInterp {
    /// Argument tuples the ground model already fixed.
    pub(crate) entries: FxHashMap<Vec<CertValue>, CertValue>,
    /// The value at every argument tuple not in `entries`.
    pub(crate) default: CertValue,
}

impl FuncInterp {
    /// The value this function takes at `args`.
    pub(crate) fn apply(&self, args: &[CertValue]) -> &CertValue {
        self.entries.get(args).unwrap_or(&self.default)
    }
}

/// A total interpretation of every symbol the assertions mention.
#[derive(Clone, Debug, Default)]
pub(crate) struct Interpretation {
    /// Uninterpreted function symbols.
    pub(crate) funcs: FxHashMap<Spur, FuncInterp>,
    /// Free (declared or Skolem) constants.
    pub(crate) consts: FxHashMap<Spur, CertValue>,
}
