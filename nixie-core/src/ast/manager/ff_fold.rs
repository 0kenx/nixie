//! Finite-field term construction with the rewriter's normal form baked in.
//!
//! Mirrors cvc5's `theory_ff_rewriter.cpp` (the read-only spec at
//! `../temp/cvc5`): every `mk_ff_*` constructor returns a term already in
//! normal form, so the encoder downstream sees canonical syntax:
//!
//! * `ff.neg t` is `(ff.mul #f(p-1) t)` (`preRewriteFfNeg`), so no `FfNeg`
//!   node survives construction;
//! * nested n-ary `add`/`mul` are flattened (`preRewriteFfAdd/Mult`);
//! * in a sum, constant summands fold into one; non-constant summands of the
//!   shape `(ff.mul c rest…)` split into scalar `c` and node `rest…`, and
//!   equal nodes accumulate their scalars (`postRewriteFfAdd`); a scalar
//!   that cancels drops the summand; scalar 1 leaves the bare node;
//! * in a product, a zero constant swallows everything and the folded
//!   constant is prepended unless it is 1 (`postRewriteFfMult`);
//! * children are ordered by `TermId` — cvc5's `std::map<Node>` ordering —
//!   so the form is canonical for hash-consing;
//! * `ff.bitsum` folds when every child is a numeral:
//!   `Σ 2ⁱ · bᵢ` evaluated in the field (`postRewriteFfBitsum`);
//! * `=` between two numerals folds to `true`/`false` and is otherwise
//!   oriented by term order (`postRewriteFfEq`) — that last rule lives in
//!   `mk_eq` (builder.rs), like the other equality folds.

use super::super::term::{TermId, TermKind};
use super::TermManager;
use crate::sort::SortId;
use crate::sort::field::FieldId;
use num_bigint::BigInt;
use num_traits::{One, Zero};
use smallvec::SmallVec;

/// Errors that can arise when building finite-field terms. Field terms are
/// built by *trusted* internal code (the encoder, the model builder) as well
/// as by the parser, so constructors return `Result`: a value that cannot
/// live in the field is a caller bug, and it must surface, not default.
#[derive(Debug, thiserror::Error)]
pub enum FfBuildError {
    /// The field is unknown to this manager (never interned).
    #[error("unknown finite field id {0:?}")]
    UnknownField(FieldId),
    /// A term id is not in the arena.
    #[error("term id {0:?} not found")]
    UnknownTerm(TermId),
    /// An operand is not finite-field sorted.
    #[error("operand {0:?} is not finite-field sorted")]
    NotFieldSorted(TermId),
    /// Operands live in different fields: a type error, not a coercion.
    #[error("operands of a finite-field operator belong to different fields")]
    FieldMismatch,
    /// No supported field representation exists for this identifier.
    #[error("finite field {0:?} is not a prime field")]
    NotPrimeField(FieldId),
    /// A binary polynomial-basis element must be nonnegative and canonical.
    #[error("noncanonical binary field element")]
    InvalidBinaryElement,
    /// An arity violation in an operator that requires ≥ 2 operands.
    #[error("finite-field operator requires at least 2 operands, got {0}")]
    TooFewOperands(usize),
}

impl TermManager {
    /// The sort of the field `field`.
    ///
    /// Errors when the field was never interned (an unknown `FieldId` would
    /// otherwise fabricate a sort whose modulus nobody established).
    pub fn ff_sort(&mut self, field: FieldId) -> Result<SortId, FfBuildError> {
        let kind = crate::sort::SortKind::FiniteField(field);
        if self.sorts.find(&kind).is_none() && self.sorts.field_desc(field).is_none() {
            return Err(FfBuildError::UnknownField(field));
        }
        Ok(self.sorts.intern(kind))
    }

    /// Intern `#f<value>m<p>` for the already-interned field `field`,
    /// reducing prime residues into `[0, p)`. For binary extensions `value`
    /// is a canonical polynomial-basis encoding, checked without reduction.
    pub fn mk_ff_const(&mut self, field: FieldId, value: BigInt) -> Result<TermId, FfBuildError> {
        let sort = self.ff_sort(field)?;
        if let Some(binary) = self.sorts.field_desc(field).and_then(|d| d.binary())
            && !value.to_biguint().is_some_and(|v| binary.contains(&v))
        {
            return Err(FfBuildError::InvalidBinaryElement);
        }
        let reduced = self
            .sorts
            .field_table()
            .reduce(field, &value)
            .ok_or(FfBuildError::NotPrimeField(field))?;
        Ok(self.intern(
            TermKind::FfConst {
                value: reduced,
                field,
            },
            sort,
        ))
    }

    /// `ff.neg t` → `(ff.mul #f(p−1) t)`; a constant negates by folding.
    pub fn mk_ff_neg(&mut self, t: TermId) -> Result<TermId, FfBuildError> {
        let kind = self
            .get(t)
            .ok_or(FfBuildError::UnknownTerm(t))?
            .kind
            .clone();
        let field = self.ff_field_of(t)?;
        if self
            .sorts
            .field_desc(field)
            .and_then(|d| d.binary())
            .is_some()
        {
            return Ok(t); // characteristic two: -a = a, not q-a
        }
        if let TermKind::FfConst { value, .. } = &kind {
            return self.mk_ff_const(field, -value.clone());
        }
        let neg_one = self.mk_ff_const(field, -BigInt::one())?;
        self.mk_ff_mul_fields(field, [neg_one, t])
    }

    /// The field a term is sorted into.
    fn ff_field_of(&self, t: TermId) -> Result<FieldId, FfBuildError> {
        let term = self.get(t).ok_or(FfBuildError::UnknownTerm(t))?;
        match self.sorts.get(term.sort).map(|s| &s.kind) {
            Some(crate::sort::SortKind::FiniteField(field)) => Ok(*field),
            _ => Err(FfBuildError::NotFieldSorted(t)),
        }
    }

    /// Flatten `ff.add`/`ff.mul` operands: a nested operator of the same
    /// kind is spliced in (`preRewriteFfAdd/Mult`). Because construction
    /// always normalizes, one level is all that can exist.
    fn ff_flatten(&self, add: bool, args: &[TermId]) -> SmallVec<[TermId; 4]> {
        let mut out: SmallVec<[TermId; 4]> = SmallVec::new();
        for &a in args {
            let same_kind = self.get(a).is_some_and(|t| match &t.kind {
                TermKind::FfAdd(_) => add,
                TermKind::FfMul(_) => !add,
                _ => false,
            });
            if same_kind
                && let Some(term) = self.get(a)
                && let TermKind::FfAdd(inner) | TermKind::FfMul(inner) = &term.kind
            {
                out.extend(inner.iter().copied());
                continue;
            }
            out.push(a);
        }
        out
    }

    /// `ff.add` over ≥ 2 operands of one field, in normal form.
    pub fn mk_ff_add(
        &mut self,
        args: impl IntoIterator<Item = TermId>,
    ) -> Result<TermId, FfBuildError> {
        let args: SmallVec<[TermId; 4]> = args.into_iter().collect();
        if args.len() < 2 {
            return Err(FfBuildError::TooFewOperands(args.len()));
        }
        let field = self.ff_field_of(args[0])?;
        self.mk_ff_add_fields(field, args)
    }

    /// `ff.add` with the field known to the caller (the internal path used
    /// by the encoder, where the operand list may be empty).
    pub fn mk_ff_add_fields(
        &mut self,
        field: FieldId,
        args: impl IntoIterator<Item = TermId>,
    ) -> Result<TermId, FfBuildError> {
        let args: SmallVec<[TermId; 4]> = args.into_iter().collect();
        if args.is_empty() {
            return self.mk_ff_const(field, BigInt::zero());
        }
        if self
            .sorts
            .field_desc(field)
            .and_then(|d| d.binary())
            .is_some()
        {
            return self.mk_binary_fold(field, args, true);
        }
        let flat = self.ff_flatten(true, &args);
        // Every operand must live in `field` — a mix is a type error.
        for &a in &flat {
            if self.ff_field_of(a)? != field {
                return Err(FfBuildError::FieldMismatch);
            }
        }

        // Fold the constant part; split `(ff.mul c rest…)` summands into
        // scalar/node pairs (cvc5's `parseScalar`).
        let mut constant = BigInt::zero();
        // (node, scalar); sorted by TermId before emission.
        let mut scalars: Vec<(TermId, BigInt)> = Vec::new();
        for &a in &flat {
            let kind = self
                .get(a)
                .ok_or(FfBuildError::UnknownTerm(a))?
                .kind
                .clone();
            match kind {
                TermKind::FfConst { value, .. } => constant += value,
                TermKind::FfMul(children) => {
                    let head_const = match self.get(children[0]).map(|t| &t.kind) {
                        Some(TermKind::FfConst { value, .. }) => Some(value.clone()),
                        _ => None,
                    };
                    let (scalar, node) = if let Some(value) = head_const {
                        let rest = &children[1..];
                        let node = if rest.len() == 1 {
                            rest[0]
                        } else {
                            self.mk_ff_mul_fields(field, rest.iter().copied())?
                        };
                        (value, node)
                    } else {
                        (BigInt::one(), a)
                    };
                    match scalars.iter_mut().find(|(n, _)| *n == node) {
                        Some((_, s)) => *s += scalar,
                        None => scalars.push((node, scalar)),
                    }
                }
                _ => match scalars.iter_mut().find(|(n, _)| *n == a) {
                    Some((_, s)) => *s += BigInt::one(),
                    None => scalars.push((a, BigInt::one())),
                },
            }
        }

        let mut summands: SmallVec<[TermId; 4]> = SmallVec::new();
        if scalars.is_empty() || !constant.is_zero() {
            summands.push(self.mk_ff_const(field, constant)?);
        }
        scalars.sort_by_key(|(node, _)| *node);
        for (node, scalar) in scalars {
            if scalar.is_zero() {
                // cancelled out
            } else if scalar.is_one() {
                summands.push(node);
            } else {
                let c = self.mk_ff_const(field, scalar)?;
                summands.push(self.mk_ff_mul_unchecked(field, smallvec::smallvec![c, node])?);
            }
        }
        if summands.is_empty() {
            return self.mk_ff_const(field, BigInt::zero());
        }
        if summands.len() == 1 {
            return Ok(summands[0]);
        }
        let sort = self.ff_sort(field)?;
        Ok(self.intern(TermKind::FfAdd(summands), sort))
    }

    /// `ff.mul` over ≥ 2 operands of one field, in normal form.
    pub fn mk_ff_mul(
        &mut self,
        args: impl IntoIterator<Item = TermId>,
    ) -> Result<TermId, FfBuildError> {
        let args: SmallVec<[TermId; 4]> = args.into_iter().collect();
        if args.len() < 2 {
            return Err(FfBuildError::TooFewOperands(args.len()));
        }
        let field = self.ff_field_of(args[0])?;
        self.mk_ff_mul_unchecked(field, args)
    }

    /// `ff.mul` with the field known to the caller.
    pub fn mk_ff_mul_fields(
        &mut self,
        field: FieldId,
        args: impl IntoIterator<Item = TermId>,
    ) -> Result<TermId, FfBuildError> {
        let args: SmallVec<[TermId; 4]> = args.into_iter().collect();
        if args.len() <= 1 {
            return match args.into_iter().next() {
                Some(a) if self.ff_field_of(a)? == field => Ok(a),
                Some(_) => Err(FfBuildError::FieldMismatch),
                None => self.mk_ff_const(field, BigInt::one()),
            };
        }
        self.mk_ff_mul_unchecked(field, args)
    }

    /// The product normal form proper. `args` is non-empty and every operand
    /// lives in `field` (checked by the public wrappers).
    fn mk_ff_mul_unchecked(
        &mut self,
        field: FieldId,
        args: SmallVec<[TermId; 4]>,
    ) -> Result<TermId, FfBuildError> {
        if self
            .sorts
            .field_desc(field)
            .and_then(|d| d.binary())
            .is_some()
        {
            return self.mk_binary_fold(field, args, false);
        }
        let flat = self.ff_flatten(false, &args);
        for &a in &flat {
            if self.ff_field_of(a)? != field {
                return Err(FfBuildError::FieldMismatch);
            }
        }
        let mut constant = BigInt::one();
        let mut factors: SmallVec<[TermId; 4]> = SmallVec::new();
        for &a in &flat {
            if let Some(TermKind::FfConst { value, .. }) = self.get(a).map(|t| &t.kind).cloned() {
                constant *= value;
            } else {
                factors.push(a);
            }
        }
        if constant.is_zero() {
            factors.clear();
        }
        let mut children: SmallVec<[TermId; 4]> = SmallVec::new();
        if !constant.is_one() || factors.is_empty() {
            children.push(self.mk_ff_const(field, constant)?);
        }
        factors.sort_unstable();
        children.extend(factors);
        if children.len() == 1 {
            return Ok(children[0]);
        }
        let sort = self.ff_sort(field)?;
        Ok(self.intern(TermKind::FfMul(children), sort))
    }

    // Extension normal form deliberately avoids the prime-field scalar collector:
    // encoded polynomial coefficients add by XOR, not integer addition.
    fn mk_binary_fold(
        &mut self,
        field: FieldId,
        args: SmallVec<[TermId; 4]>,
        add: bool,
    ) -> Result<TermId, FfBuildError> {
        let binary = self
            .sorts
            .field_desc(field)
            .and_then(|d| d.binary())
            .ok_or(FfBuildError::UnknownField(field))?
            .clone();
        let flat = self.ff_flatten(add, &args);
        let mut constant = num_bigint::BigUint::from(u8::from(!add));
        let mut children: SmallVec<[TermId; 4]> = SmallVec::new();
        for a in flat {
            if self.ff_field_of(a)? != field {
                return Err(FfBuildError::FieldMismatch);
            }
            match &self.get(a).ok_or(FfBuildError::UnknownTerm(a))?.kind {
                TermKind::FfConst { value, .. } => {
                    let value = value
                        .to_biguint()
                        .ok_or(FfBuildError::InvalidBinaryElement)?;
                    constant = if add {
                        binary.add(&constant, &value)
                    } else {
                        binary.mul(&constant, &value)
                    }
                    .ok_or(FfBuildError::InvalidBinaryElement)?;
                }
                _ => children.push(a),
            }
        }
        if !add && constant.is_zero() {
            children.clear();
        }
        children.sort_unstable();
        if children.is_empty() || (add && !constant.is_zero()) || (!add && !constant.is_one()) {
            let c = self.mk_ff_const(field, BigInt::from(constant))?;
            children.insert(0, c);
        }
        if children.len() == 1 {
            return Ok(children[0]);
        }
        let sort = self.ff_sort(field)?;
        let kind = if add {
            TermKind::FfAdd(children)
        } else {
            TermKind::FfMul(children)
        };
        Ok(self.intern(kind, sort))
    }

    /// `ff.bitsum` over ≥ 2 field-element operands (little-endian), folding
    /// when every child is a numeral.
    pub fn mk_ff_bitsum(
        &mut self,
        args: impl IntoIterator<Item = TermId>,
    ) -> Result<TermId, FfBuildError> {
        let args: SmallVec<[TermId; 4]> = args.into_iter().collect();
        if args.len() < 2 {
            return Err(FfBuildError::TooFewOperands(args.len()));
        }
        let field = self.ff_field_of(args[0])?;
        for &a in &args {
            if self.ff_field_of(a)? != field {
                return Err(FfBuildError::FieldMismatch);
            }
        }
        if self
            .sorts
            .field_desc(field)
            .and_then(|d| d.binary())
            .is_some()
        {
            // The coefficient 2 is 1+1=0, NOT the polynomial-basis value X.
            return Ok(args[0]);
        }
        // All-constant: Σ 2ⁱ bᵢ evaluated in the field.
        let mut acc = BigInt::zero();
        let mut multiplier = BigInt::one();
        let mut all_const = true;
        for &a in &args {
            if let Some(TermKind::FfConst { value, .. }) = self.get(a).map(|t| &t.kind).cloned() {
                acc += &multiplier * &value;
            } else {
                all_const = false;
                break;
            }
            multiplier *= 2;
        }
        if all_const {
            return self.mk_ff_const(field, acc);
        }
        let sort = self.ff_sort(field)?;
        Ok(self.intern(TermKind::FfBitsum(args), sort))
    }

    /// `=` over two finite-field terms: fold numeral comparisons, orient by
    /// term order otherwise. Returns `None` when neither side is
    /// field-sorted, so `mk_eq` can fall through to its generic handling.
    pub(crate) fn mk_ff_eq(&mut self, lhs: TermId, rhs: TermId) -> Option<TermId> {
        let field = self.ff_field_of(lhs).ok()?;
        if self.ff_field_of(rhs).ok()? != field {
            return None;
        }
        let lk = self.get(lhs).map(|t| t.kind.clone());
        let rk = self.get(rhs).map(|t| t.kind.clone());
        if let (
            Some(TermKind::FfConst { value: a, .. }),
            Some(TermKind::FfConst { value: b, .. }),
        ) = (&lk, &rk)
        {
            return Some(self.mk_bool(a == b));
        }
        // Orient by term order: canonical for hash-consing and for the
        // encoder's `p(x) = 0` form.
        let (l, r) = if lhs <= rhs { (lhs, rhs) } else { (rhs, lhs) };
        Some(self.intern(TermKind::Eq(l, r), self.sorts.bool_sort))
    }
}

impl TermManager {
    /// Rebuild a finite-field node whose children were substituted.
    ///
    /// Used by the substitution walkers (`query/substitute.rs`,
    /// `ematching/substitution/apply.rs`), which must return a `TermId`, not
    /// a `Result`. The normal-form builders are tried first; if they refuse
    /// (which for an interned, well-typed node cannot happen — the only
    /// failure modes are field mismatches and dangling ids, both excluded by
    /// the term having been interned at one field sort), the node is
    /// re-interned with its substituted children verbatim. That fallback is
    /// still *semantically exact* — `ff.add` applied to substituted operands
    /// is the substituted sum — it only loses the folded normal form, which
    /// every consumer re-establishes through the builders. Total, no
    /// `unwrap`, and never a fabricated value.
    pub fn intern_ff_substituted(&mut self, kind: TermKind, sort: SortId) -> TermId {
        let field = match &kind {
            TermKind::FfConst { field, .. } => Some(*field),
            TermKind::FfAdd(args) | TermKind::FfMul(args) | TermKind::FfBitsum(args) => args
                .first()
                .and_then(|&a| self.get(a))
                .and_then(|t| match self.sorts.get(t.sort).map(|s| &s.kind) {
                    Some(crate::sort::SortKind::FiniteField(field)) => Some(*field),
                    _ => None,
                }),
            TermKind::FfNeg(a) => {
                self.get(*a)
                    .and_then(|t| match self.sorts.get(t.sort).map(|s| &s.kind) {
                        Some(crate::sort::SortKind::FiniteField(field)) => Some(*field),
                        _ => None,
                    })
            }
            _ => None,
        };
        let rebuilt = match (&kind, field) {
            (TermKind::FfAdd(args), Some(field)) => {
                let args = args.clone();
                self.mk_ff_add_fields(field, args).ok()
            }
            (TermKind::FfMul(args), Some(field)) => {
                let args = args.clone();
                self.mk_ff_mul_fields(field, args).ok()
            }
            (TermKind::FfBitsum(args), _) => {
                let args = args.clone();
                self.mk_ff_bitsum(args).ok()
            }
            (TermKind::FfNeg(a), _) => self.mk_ff_neg(*a).ok(),
            _ => None,
        };
        rebuilt.unwrap_or_else(|| self.intern_term(kind, sort))
    }
}
