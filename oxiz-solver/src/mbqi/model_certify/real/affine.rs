//! Affine forms over one real variable and the finite partitions of `ℝ` the
//! real certifier computes with.
//!
//! Every value the real engine produces is *piecewise affine*: the real line is
//! cut at finitely many rationals, and on each resulting cell (a cut point, or
//! an open interval between two neighbouring cuts) the value is either a single
//! affine form `a·x + b` or a single boolean.  That representation is exact —
//! no sampling is involved — which is what lets a `∀` over an *infinite* domain
//! be decided by inspecting finitely many cells.

use num_rational::BigRational;
use num_traits::{One, Zero};

#[allow(unused_imports)]
use crate::prelude::*;

/// The exact rational the real engine computes with.
pub(crate) type Rat = BigRational;

/// An affine function `a·x + b` of the single bound variable `x`.
///
/// A constant is the `a = 0` case, so ground sub-terms and quantified ones live
/// in the same domain and need no special casing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Affine {
    /// Coefficient of the bound variable.
    pub(crate) a: Rat,
    /// Constant term.
    pub(crate) b: Rat,
}

impl Affine {
    /// The constant function `x ↦ value`.
    pub(crate) fn constant(value: Rat) -> Self {
        Self {
            a: Rat::zero(),
            b: value,
        }
    }

    /// The identity `x ↦ x`.
    pub(crate) fn identity() -> Self {
        Self {
            a: Rat::one(),
            b: Rat::zero(),
        }
    }

    /// The constant value of this form, or `None` when it really depends on
    /// `x`.
    pub(crate) fn as_constant(&self) -> Option<&Rat> {
        if self.a.is_zero() {
            Some(&self.b)
        } else {
            None
        }
    }

    /// The value of this form at `x`.
    pub(crate) fn eval(&self, x: &Rat) -> Rat {
        &self.a * x + &self.b
    }

    /// `self + other`.
    pub(crate) fn add(&self, other: &Self) -> Self {
        Self {
            a: &self.a + &other.a,
            b: &self.b + &other.b,
        }
    }

    /// `self - other`.
    pub(crate) fn sub(&self, other: &Self) -> Self {
        Self {
            a: &self.a - &other.a,
            b: &self.b - &other.b,
        }
    }

    /// `-self`.
    pub(crate) fn neg(&self) -> Self {
        Self {
            a: -self.a.clone(),
            b: -self.b.clone(),
        }
    }

    /// `self · other`, or `None` when both factors genuinely depend on `x`.
    ///
    /// Declining the non-linear case is what keeps every value affine, and with
    /// it the completeness argument of [`Partition`]: a quadratic could change
    /// sign twice inside one cell.
    pub(crate) fn mul(&self, other: &Self) -> Option<Self> {
        let (scale, form) = match (self.as_constant(), other.as_constant()) {
            (Some(k), _) => (k, other),
            (None, Some(k)) => (k, self),
            (None, None) => return None,
        };
        Some(Self {
            a: scale * &form.a,
            b: scale * &form.b,
        })
    }

    /// `self / other`, or `None` when the divisor is not a non-zero constant.
    pub(crate) fn div(&self, other: &Self) -> Option<Self> {
        let k = other.as_constant()?;
        if k.is_zero() {
            return None;
        }
        Some(Self {
            a: &self.a / k,
            b: &self.b / k,
        })
    }

    /// `self ∘ inner`, i.e. `x ↦ self(inner(x))`.
    ///
    /// This is how an uninterpreted function's affine default is applied to an
    /// argument that is itself affine in `x` — the composition that decides
    /// nested applications such as `f(g(x))`.
    pub(crate) fn compose(&self, inner: &Self) -> Self {
        Self {
            a: &self.a * &inner.a,
            b: &self.a * &inner.b + &self.b,
        }
    }

    /// The unique `x` with `a·x + b = 0`, or `None` when the form is constant.
    pub(crate) fn root(&self) -> Option<Rat> {
        if self.a.is_zero() {
            None
        } else {
            Some(-&self.b / &self.a)
        }
    }
}

/// A finite partition of `ℝ` into cut points and the open intervals between
/// them.
///
/// With cuts `c₀ < c₁ < … < c_{n-1}` the cells are, in order,
///
/// ```text
/// (-∞, c₀)  {c₀}  (c₀, c₁)  {c₁}  …  {c_{n-1}}  (c_{n-1}, +∞)
/// ```
///
/// — `2n + 1` of them, every one non-empty.  Non-emptiness is the whole point:
/// "the body holds on every cell" is then *equivalent* to "the body holds for
/// every real", not merely implied by it.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Partition {
    /// Strictly increasing cut points.
    cuts: Vec<Rat>,
}

impl Partition {
    /// The trivial partition: one cell, the whole line.
    pub(crate) fn whole() -> Self {
        Self { cuts: Vec::new() }
    }

    /// The partition cut at `points` (which need not be sorted or distinct).
    pub(crate) fn from_points(mut points: Vec<Rat>) -> Self {
        points.sort();
        points.dedup();
        Self { cuts: points }
    }

    /// The number of cells.
    pub(crate) fn len(&self) -> usize {
        self.cuts.len() * 2 + 1
    }

    /// The cut points.
    pub(crate) fn cuts(&self) -> &[Rat] {
        &self.cuts
    }

    /// This partition refined by `extra` cut points.
    pub(crate) fn refined_by(&self, extra: &[Rat]) -> Self {
        if extra.is_empty() {
            return self.clone();
        }
        let mut points = self.cuts.clone();
        points.extend(extra.iter().cloned());
        Self::from_points(points)
    }

    /// The coarsest partition refining both `self` and `other`.
    pub(crate) fn merge(&self, other: &Self) -> Self {
        if other.cuts.is_empty() {
            return self.clone();
        }
        self.refined_by(&other.cuts)
    }

    /// A point of cell `index` together with whether that cell is a single
    /// point.
    ///
    /// For an open cell the point returned lies *strictly* inside it and is
    /// never a cut of this partition — which is what lets [`Piecewise::refine`]
    /// locate a refined cell inside its coarser ancestor by value alone.
    pub(crate) fn probe(&self, index: usize) -> Option<(Rat, bool)> {
        if index >= self.len() {
            return None;
        }
        if index % 2 == 1 {
            return self.cuts.get(index / 2).map(|c| (c.clone(), true));
        }
        let slot = index / 2;
        let lower = slot.checked_sub(1).and_then(|i| self.cuts.get(i));
        let upper = self.cuts.get(slot);
        let point = match (lower, upper) {
            (None, None) => Rat::zero(),
            (None, Some(hi)) => hi - Rat::one(),
            (Some(lo), None) => lo + Rat::one(),
            (Some(lo), Some(hi)) => (lo + hi) / Rat::from_integer(2.into()),
        };
        Some((point, false))
    }

    /// Whether `point` lies strictly inside the open cell `index`.
    ///
    /// A point cell contains no interior, so this is `false` for odd indices.
    pub(crate) fn strictly_inside(&self, index: usize, point: &Rat) -> bool {
        if index % 2 == 1 || index >= self.len() {
            return false;
        }
        let slot = index / 2;
        let above_lower = match slot.checked_sub(1).and_then(|i| self.cuts.get(i)) {
            Some(lo) => point > lo,
            None => true,
        };
        let below_upper = match self.cuts.get(slot) {
            Some(hi) => point < hi,
            None => true,
        };
        above_lower && below_upper
    }

    /// The index of the cell of this partition that contains `point`.
    ///
    /// Whether the caller meant a point cell or an interior sample need not be
    /// passed in, and that is exactly the invariant refinement rests on: an
    /// interior sample of a *finer* partition is never one of this coarser
    /// partition's cuts (see [`Partition::probe`]), so landing on a cut can
    /// only mean a point cell and landing between cuts can only mean the open
    /// cell there.
    fn locate(&self, point: &Rat) -> usize {
        match self.cuts.binary_search(point) {
            Ok(slot) => slot * 2 + 1,
            Err(slot) => slot * 2,
        }
    }
}

/// A value defined cell-by-cell over a [`Partition`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Piecewise<T> {
    part: Partition,
    cells: Vec<T>,
}

impl<T: Clone> Piecewise<T> {
    /// The value `cell` on every real.
    pub(crate) fn uniform(cell: T) -> Self {
        Self {
            part: Partition::whole(),
            cells: vec![cell],
        }
    }

    /// Build from a partition and one value per cell, or `None` on a length
    /// mismatch.
    pub(crate) fn new(part: Partition, cells: Vec<T>) -> Option<Self> {
        if cells.len() == part.len() {
            Some(Self { part, cells })
        } else {
            None
        }
    }

    /// The partition this value is defined over.
    pub(crate) fn partition(&self) -> &Partition {
        &self.part
    }

    /// The per-cell values, in cell order.
    pub(crate) fn cells(&self) -> &[T] {
        &self.cells
    }

    /// This value re-expressed over the finer partition `part`.
    ///
    /// `part` must refine `self.part`; every cell of `part` then lies wholly
    /// inside one cell of `self.part`, so the re-expression is exact rather
    /// than an approximation.
    pub(crate) fn refine(&self, part: &Partition) -> Option<Self> {
        if part == &self.part {
            return Some(self.clone());
        }
        let mut cells = Vec::with_capacity(part.len());
        for index in 0..part.len() {
            let (point, _) = part.probe(index)?;
            let source = self.part.locate(&point);
            cells.push(self.cells.get(source)?.clone());
        }
        Self::new(part.clone(), cells)
    }
}

/// Re-express `left` and `right` over their common refinement.
pub(crate) fn align<A: Clone, B: Clone>(
    left: &Piecewise<A>,
    right: &Piecewise<B>,
) -> Option<(Piecewise<A>, Piecewise<B>)> {
    let part = left.partition().merge(right.partition());
    Some((left.refine(&part)?, right.refine(&part)?))
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    fn rat(numer: i64, denom: i64) -> Rat {
        Rat::new(BigInt::from(numer), BigInt::from(denom))
    }

    #[test]
    fn whole_partition_has_one_cell() {
        let part = Partition::whole();
        assert_eq!(part.len(), 1);
        assert_eq!(part.probe(0), Some((rat(0, 1), false)));
        assert_eq!(part.probe(1), None);
    }

    #[test]
    fn cells_alternate_interval_and_point() {
        let part = Partition::from_points(vec![rat(0, 1), rat(10, 1)]);
        assert_eq!(part.len(), 5);
        assert_eq!(part.probe(0), Some((rat(-1, 1), false)));
        assert_eq!(part.probe(1), Some((rat(0, 1), true)));
        assert_eq!(part.probe(2), Some((rat(5, 1), false)));
        assert_eq!(part.probe(3), Some((rat(10, 1), true)));
        assert_eq!(part.probe(4), Some((rat(11, 1), false)));
    }

    #[test]
    fn interior_probes_are_never_cuts() {
        let part = Partition::from_points(vec![rat(-3, 2), rat(1, 3), rat(7, 5)]);
        for index in (0..part.len()).step_by(2) {
            let (point, is_point) = part.probe(index).expect("cell exists");
            assert!(!is_point);
            assert!(!part.cuts().contains(&point), "interior probe hit a cut");
            assert!(part.strictly_inside(index, &point));
        }
    }

    #[test]
    fn refine_preserves_values_pointwise() {
        let coarse = Partition::from_points(vec![rat(0, 1)]);
        let value = Piecewise::new(coarse, vec![1i32, 2, 3]).expect("well formed");
        let finer = Partition::from_points(vec![rat(-1, 1), rat(0, 1), rat(5, 1)]);
        let refined = value.refine(&finer).expect("refinement");
        // (-inf,-1) -1 (-1,0) all sit in the coarse cell (-inf,0) -> 1
        assert_eq!(refined.cells()[0], 1);
        assert_eq!(refined.cells()[1], 1);
        assert_eq!(refined.cells()[2], 1);
        // {0} is the coarse point cell -> 2
        assert_eq!(refined.cells()[3], 2);
        // everything above 0 is the coarse cell (0,inf) -> 3
        assert_eq!(refined.cells()[4], 3);
        assert_eq!(refined.cells()[5], 3);
        assert_eq!(refined.cells()[6], 3);
    }

    #[test]
    fn align_puts_both_sides_on_one_partition() {
        let left = Piecewise::new(Partition::from_points(vec![rat(1, 1)]), vec![10i32, 20, 30])
            .expect("well formed");
        let right = Piecewise::new(Partition::from_points(vec![rat(2, 1)]), vec![7i32, 8, 9])
            .expect("well formed");
        let (l, r) = align(&left, &right).expect("aligned");
        assert_eq!(l.partition(), r.partition());
        assert_eq!(l.cells().len(), 5);
    }

    #[test]
    fn affine_composition_matches_pointwise_evaluation() {
        let outer = Affine {
            a: rat(2, 1),
            b: rat(1, 1),
        };
        let inner = Affine {
            a: rat(3, 1),
            b: rat(-4, 1),
        };
        let composed = outer.compose(&inner);
        for k in -3..4 {
            let x = rat(k, 1);
            assert_eq!(composed.eval(&x), outer.eval(&inner.eval(&x)));
        }
    }

    #[test]
    fn affine_mul_declines_quadratics() {
        let x = Affine::identity();
        assert!(x.mul(&x).is_none());
        assert!(x.mul(&Affine::constant(rat(3, 1))).is_some());
    }

    #[test]
    fn affine_root_is_exact() {
        let form = Affine {
            a: rat(2, 1),
            b: rat(-7, 1),
        };
        let root = form.root().expect("non-constant");
        assert_eq!(root, rat(7, 2));
        assert!(form.eval(&root).is_zero());
        assert!(Affine::constant(rat(5, 1)).root().is_none());
    }
}
