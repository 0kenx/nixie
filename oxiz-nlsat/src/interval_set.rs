//! Interval sets for NLSAT.
//!
//! This module provides interval set representation for tracking feasible
//! regions in the NLSAT solver. An interval set is a union of disjoint
//! intervals, used to represent the possible values for a variable.
//!
//! Reference: Z3's `nlsat/nlsat_interval_set.cpp`

use num_rational::BigRational;
use num_traits::{One, Zero};
use oxiz_math::interval::{Bound, Interval};
use std::fmt;

/// Kind of polynomial constraint.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstraintKind {
    /// Equality: p = 0
    Eq,
    /// Less than: p < 0
    Lt,
    /// Greater than: p > 0
    Gt,
    /// Less or equal: p <= 0
    Le,
    /// Greater or equal: p >= 0
    Ge,
    /// Not equal: p != 0
    Ne,
}

/// An interval set is a union of disjoint intervals.
#[derive(Clone, Debug)]
pub struct IntervalSet {
    /// Disjoint intervals in sorted order (by lower bound).
    intervals: Vec<Interval>,
}

impl IntervalSet {
    /// Create an empty interval set.
    #[inline]
    pub fn empty() -> Self {
        Self {
            intervals: Vec::new(),
        }
    }

    /// Create the full interval set (-∞, +∞).
    pub fn reals() -> Self {
        Self {
            intervals: vec![Interval::reals()],
        }
    }

    /// Create a singleton interval set containing just one point.
    pub fn point(a: BigRational) -> Self {
        Self {
            intervals: vec![Interval::point(a)],
        }
    }

    /// Alias for `point()`.
    #[inline]
    pub fn from_point(a: BigRational) -> Self {
        Self::point(a)
    }

    /// Create interval set for x < a: (-∞, a).
    pub fn lt(a: BigRational) -> Self {
        Self {
            intervals: vec![Interval::less_than(a)],
        }
    }

    /// Create interval set for x <= a: (-∞, a].
    pub fn le(a: BigRational) -> Self {
        Self {
            intervals: vec![Interval::at_most(a)],
        }
    }

    /// Create interval set for x > a: (a, +∞).
    pub fn gt(a: BigRational) -> Self {
        Self {
            intervals: vec![Interval::greater_than(a)],
        }
    }

    /// Create interval set for x >= a: [a, +∞).
    pub fn ge(a: BigRational) -> Self {
        Self {
            intervals: vec![Interval::at_least(a)],
        }
    }

    /// Create from a single interval.
    pub fn from_interval(interval: Interval) -> Self {
        if interval.is_empty() {
            Self::empty()
        } else {
            Self {
                intervals: vec![interval],
            }
        }
    }

    /// Create from multiple intervals (normalizes them).
    pub fn from_intervals(intervals: impl IntoIterator<Item = Interval>) -> Self {
        let mut set = Self::empty();
        for interval in intervals {
            set = set.union(&Self::from_interval(interval));
        }
        set
    }

    /// Check if the set is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.intervals.is_empty()
    }

    /// Check if the set is the full real line.
    pub fn is_reals(&self) -> bool {
        self.intervals.len() == 1
            && self.intervals[0].lo.is_neg_inf()
            && self.intervals[0].hi.is_pos_inf()
    }

    /// Check if the set contains a single point.
    pub fn is_singleton(&self) -> bool {
        self.intervals.len() == 1 && self.intervals[0].is_point()
    }

    /// Get the number of intervals.
    #[inline]
    pub fn num_intervals(&self) -> usize {
        self.intervals.len()
    }

    /// Get the intervals.
    #[inline]
    pub fn intervals(&self) -> &[Interval] {
        &self.intervals
    }

    /// Check if the set contains a value.
    pub fn contains(&self, x: &BigRational) -> bool {
        self.intervals.iter().any(|i| i.contains(x))
    }

    /// Check if the set contains zero.
    pub fn contains_zero(&self) -> bool {
        self.contains(&BigRational::zero())
    }

    /// Get the lower bound of the set.
    pub fn lower_bound(&self) -> Option<&Bound> {
        self.intervals.first().map(|i| &i.lo)
    }

    /// Get the upper bound of the set.
    pub fn upper_bound(&self) -> Option<&Bound> {
        self.intervals.last().map(|i| &i.hi)
    }

    /// Compute the union of two interval sets.
    pub fn union(&self, other: &IntervalSet) -> IntervalSet {
        if self.is_empty() {
            return other.clone();
        }
        if other.is_empty() {
            return self.clone();
        }

        // Merge the two sorted lists
        let mut result = Vec::with_capacity(self.intervals.len() + other.intervals.len());
        let mut i = 0;
        let mut j = 0;

        while i < self.intervals.len() && j < other.intervals.len() {
            if self.intervals[i].lo <= other.intervals[j].lo {
                result.push(self.intervals[i].clone());
                i += 1;
            } else {
                result.push(other.intervals[j].clone());
                j += 1;
            }
        }
        result.extend_from_slice(&self.intervals[i..]);
        result.extend_from_slice(&other.intervals[j..]);

        // Merge overlapping intervals
        let merged = merge_intervals(result);
        IntervalSet { intervals: merged }
    }

    /// Compute the intersection of two interval sets.
    pub fn intersect(&self, other: &IntervalSet) -> IntervalSet {
        if self.is_empty() || other.is_empty() {
            return IntervalSet::empty();
        }

        let mut result = Vec::new();
        let mut i = 0;
        let mut j = 0;

        while i < self.intervals.len() && j < other.intervals.len() {
            let intersection = self.intervals[i].intersect(&other.intervals[j]);
            if !intersection.is_empty() {
                result.push(intersection);
            }

            // Advance the iterator with the smaller upper bound
            if self.intervals[i].hi <= other.intervals[j].hi {
                i += 1;
            } else {
                j += 1;
            }
        }

        IntervalSet { intervals: result }
    }

    /// Compute the complement of the interval set.
    pub fn complement(&self) -> IntervalSet {
        if self.is_empty() {
            return IntervalSet::reals();
        }

        let mut result = Vec::new();
        let mut prev_hi = Bound::NegInf;
        let mut prev_hi_open = true;

        for interval in &self.intervals {
            // Add gap before this interval
            let gap_hi = interval.lo.clone();
            let gap_hi_open = !interval.lo_open;

            // Create gap from previous interval's end to this interval's start
            let gap = Interval {
                lo: prev_hi.clone(),
                hi: gap_hi,
                lo_open: !prev_hi_open,
                hi_open: gap_hi_open,
            };
            if !gap.is_empty() {
                result.push(gap);
            }

            prev_hi = interval.hi.clone();
            prev_hi_open = interval.hi_open;
        }

        // Add final gap to +∞
        if prev_hi < Bound::PosInf {
            result.push(Interval {
                lo: prev_hi,
                hi: Bound::PosInf,
                lo_open: !prev_hi_open,
                hi_open: true,
            });
        }

        IntervalSet { intervals: result }
    }

    /// Compute the difference: self - other.
    pub fn difference(&self, other: &IntervalSet) -> IntervalSet {
        self.intersect(&other.complement())
    }

    /// Get a sample point from the interval set (if non-empty).
    pub fn sample(&self) -> Option<BigRational> {
        if self.is_empty() {
            return None;
        }

        // Try to find a nice point (preferably an integer)
        for interval in &self.intervals {
            if let Some(mid) = interval.midpoint() {
                // Round to nearest integer if possible
                let floor = mid.floor();
                let ceil = mid.ceil();

                if interval.contains(&floor) {
                    return Some(floor);
                }
                if interval.contains(&ceil) {
                    return Some(ceil);
                }
                return Some(mid);
            }
        }

        // Handle unbounded intervals
        for interval in &self.intervals {
            // If unbounded below, try 0 or a negative integer
            if interval.lo.is_neg_inf()
                && let Bound::Finite(hi) = &interval.hi
            {
                let val = hi.floor() - BigRational::one();
                if interval.contains(&val) {
                    return Some(val);
                }
            }
            // If unbounded above, try 0 or a positive integer
            if interval.hi.is_pos_inf()
                && let Bound::Finite(lo) = &interval.lo
            {
                let val = lo.ceil() + BigRational::one();
                if interval.contains(&val) {
                    return Some(val);
                }
            }
        }

        // Just return 0 if it's in the set
        if self.contains_zero() {
            return Some(BigRational::zero());
        }

        None
    }

    /// The first point of this set that `exclude` does not already list.
    ///
    /// This is what lets the search revise an arithmetic witness (see
    /// `solver/resample.rs`): when the point an earlier variable was given
    /// turns out to leave a later, coupled variable no room at all, the same
    /// region is asked for a different one. Repeated calls with a growing
    /// `exclude` therefore walk a region's points one at a time.
    ///
    /// The order comes from `Self::witness_candidates`, which offers
    /// "nicer" points first — integers before fractions, small before large,
    /// and nonzero before zero, since a first witness of `0` is exactly what
    /// collapses a product constraint like `x·y = c` into an unsatisfiable
    /// one. Every candidate is filtered against membership, so an offer that
    /// falls outside the set simply does not count.
    ///
    /// `None` means the enumeration is spent — **not** that the set is empty.
    /// The candidate stream is deliberately finite (an unbounded region holds
    /// unboundedly many points, and something has to stop), so the caller must
    /// read exhaustion as incompleteness and never as a proof.
    pub fn sample_avoiding(&self, exclude: &[BigRational]) -> Option<BigRational> {
        if self.is_empty() {
            return None;
        }
        let spent: std::collections::HashSet<&BigRational> = exclude.iter().collect();
        self.witness_candidates()
            .find(|point| !spent.contains(point) && self.contains(point))
    }

    /// Every point this module is willing to offer as a witness, best first
    /// and lazily: nothing beyond the point a caller settles on is computed.
    ///
    /// Candidates are only *proposed* — membership is the caller's filter, so
    /// a stage may over-offer freely (a magnitude that misses the set, an
    /// integer landing in an open endpoint) rather than having to be exact.
    fn witness_candidates(&self) -> impl Iterator<Item = BigRational> + '_ {
        // Integers of the bounded components come first because a bounded
        // component is where the answer usually is and where the enumeration
        // can be near-complete. The magnitude ladder then covers rays and the
        // whole line, which have no endpoints to work inward from. Fractions
        // are last: a region too narrow to hold an integer is real, but rare,
        // and an integer witness keeps later polynomial arithmetic small.
        edgewise_integers(self)
            .chain(magnitude_ladder())
            .chain(std::iter::once(BigRational::zero()))
            .chain(dyadic_interior_points(self))
            .chain(outward_along_rays(self))
    }

    /// The set's components with finite bounds on both sides, as `(lo, hi)`
    /// pairs. Open endpoints are reported as-is; membership filtering at the
    /// point of use is what keeps an excluded endpoint out.
    fn bounded_components(&self) -> impl Iterator<Item = (&BigRational, &BigRational)> + '_ {
        self.intervals
            .iter()
            .filter_map(|interval| match (&interval.lo, &interval.hi) {
                (Bound::Finite(lo), Bound::Finite(hi)) => Some((lo, hi)),
                _ => None,
            })
    }

    /// `Some(point)` when this set is exactly one closed singleton interval,
    /// i.e. the region leaves no freedom at all (its value was forced by the
    /// intersected constraints rather than chosen).
    pub fn as_forced_point(&self) -> Option<BigRational> {
        if self.intervals.len() != 1 {
            return None;
        }
        let interval = &self.intervals[0];
        match (&interval.lo, &interval.hi) {
            (Bound::Finite(lo), Bound::Finite(hi))
                if lo == hi && !interval.lo_open && !interval.hi_open =>
            {
                Some(lo.clone())
            }
            _ => None,
        }
    }

    /// Get all finite endpoints in the interval set.
    pub fn endpoints(&self) -> Vec<BigRational> {
        let mut result = Vec::new();
        for interval in &self.intervals {
            if let Bound::Finite(lo) = &interval.lo {
                result.push(lo.clone());
            }
            if let Bound::Finite(hi) = &interval.hi
                && Some(hi) != interval.lo.as_finite()
            {
                result.push(hi.clone());
            }
        }
        result.sort();
        result.dedup();
        result
    }

    /// Intersect with the roots of a polynomial.
    ///
    /// Returns an interval set containing only the points in this set that are roots
    /// of the given polynomial. This is useful for constraint solving.
    pub fn intersect_with_roots(&self, roots: &[BigRational]) -> IntervalSet {
        if self.is_empty() || roots.is_empty() {
            return IntervalSet::empty();
        }

        let mut result_intervals = Vec::new();

        for root in roots {
            if self.contains(root) {
                result_intervals.push(Interval::point(root.clone()));
            }
        }

        IntervalSet {
            intervals: result_intervals,
        }
    }

    /// Filter this interval set by a predicate on polynomial signs.
    ///
    /// Given the roots of a polynomial and the signs between roots,
    /// returns the subset of this interval set where the polynomial has the given sign.
    pub fn filter_by_sign(
        &self,
        roots: &[BigRational],
        signs_between: &[i8],
        target_sign: i8,
    ) -> IntervalSet {
        // Create the sign-based interval set
        let sign_set = IntervalSet::sign_set(roots, signs_between, target_sign);

        // Intersect with our current set
        self.intersect(&sign_set)
    }

    /// Compute the interval set where a polynomial constraint is satisfied.
    ///
    /// Given:
    /// - roots: The roots of the polynomial
    /// - signs: The signs of the polynomial in intervals between roots
    /// - constraint: The kind of constraint (Eq, Lt, Gt)
    ///
    /// Returns the interval set satisfying the constraint.
    pub fn from_constraint(
        roots: &[BigRational],
        signs_between: &[i8],
        constraint_kind: ConstraintKind,
    ) -> IntervalSet {
        match constraint_kind {
            ConstraintKind::Eq => {
                // p = 0: just the roots
                IntervalSet::sign_set(roots, signs_between, 0)
            }
            ConstraintKind::Lt => {
                // p < 0: negative regions
                IntervalSet::sign_set(roots, signs_between, -1)
            }
            ConstraintKind::Gt => {
                // p > 0: positive regions
                IntervalSet::sign_set(roots, signs_between, 1)
            }
            ConstraintKind::Le => {
                // p <= 0: negative regions + roots
                let neg = IntervalSet::sign_set(roots, signs_between, -1);
                let zero = IntervalSet::sign_set(roots, signs_between, 0);
                neg.union(&zero)
            }
            ConstraintKind::Ge => {
                // p >= 0: positive regions + roots
                let pos = IntervalSet::sign_set(roots, signs_between, 1);
                let zero = IntervalSet::sign_set(roots, signs_between, 0);
                pos.union(&zero)
            }
            ConstraintKind::Ne => {
                // p != 0: complement of roots
                let zero = IntervalSet::sign_set(roots, signs_between, 0);
                zero.complement()
            }
        }
    }

    /// Create the interval set where a polynomial has a given sign.
    /// sign: 1 for positive, -1 for negative, 0 for zero
    pub fn sign_set(roots: &[BigRational], signs_between: &[i8], target_sign: i8) -> IntervalSet {
        if roots.is_empty() {
            // No roots, constant sign
            if signs_between.len() == 1 && signs_between[0] == target_sign {
                return IntervalSet::reals();
            }
            return IntervalSet::empty();
        }

        let mut intervals = Vec::new();
        let n = roots.len();

        // Check region before first root
        if !signs_between.is_empty() && signs_between[0] == target_sign {
            intervals.push(Interval::less_than(roots[0].clone()));
        }

        // Check each root
        for (i, root) in roots.iter().enumerate() {
            if target_sign == 0 {
                intervals.push(Interval::point(root.clone()));
            }

            // Check region after this root
            if i + 1 < signs_between.len() && signs_between[i + 1] == target_sign {
                if i + 1 < n {
                    intervals.push(Interval::open(root.clone(), roots[i + 1].clone()));
                } else {
                    intervals.push(Interval::greater_than(root.clone()));
                }
            }
        }

        IntervalSet::from_intervals(intervals)
    }

    /// Restrict to integers (for integer arithmetic).
    /// Returns the interval set of integers within this set.
    ///
    /// For a closed lower bound `lo`, the smallest admissible integer is
    /// `ceil(lo)`. For an *open* lower bound, `ceil(lo)` is wrong whenever
    /// `lo` is itself an integer (it would return `lo`, which the open
    /// bound excludes), so the smallest admissible integer is instead
    /// `floor(lo) + 1` (equivalent to `ceil(lo)` when `lo` is non-integer,
    /// and always `> lo`). The mirror argument applies to the upper bound:
    /// closed uses `floor(hi)`, open uses `ceil(hi) - 1`.
    pub fn restrict_to_integers(&self) -> IntervalSet {
        let mut result = Vec::new();

        let lo_bound_int = |lo: &BigRational, lo_open: bool| -> BigRational {
            if lo_open {
                lo.floor() + BigRational::one()
            } else {
                lo.ceil()
            }
        };
        let hi_bound_int = |hi: &BigRational, hi_open: bool| -> BigRational {
            if hi_open {
                hi.ceil() - BigRational::one()
            } else {
                hi.floor()
            }
        };

        for interval in &self.intervals {
            match (&interval.lo, &interval.hi) {
                (Bound::Finite(lo), Bound::Finite(hi)) => {
                    let lo_int = lo_bound_int(lo, interval.lo_open);
                    let hi_int = hi_bound_int(hi, interval.hi_open);

                    if lo_int <= hi_int {
                        result.push(Interval::closed(lo_int, hi_int));
                    }
                }
                (Bound::NegInf, Bound::Finite(hi)) => {
                    let hi_int = hi_bound_int(hi, interval.hi_open);
                    result.push(Interval::at_most(hi_int));
                }
                (Bound::Finite(lo), Bound::PosInf) => {
                    let lo_int = lo_bound_int(lo, interval.lo_open);
                    result.push(Interval::at_least(lo_int));
                }
                (Bound::NegInf, Bound::PosInf) => {
                    return IntervalSet::reals();
                }
                _ => {}
            }
        }

        IntervalSet { intervals: result }
    }
}

/// Merge overlapping or adjacent intervals.
fn merge_intervals(mut intervals: Vec<Interval>) -> Vec<Interval> {
    if intervals.is_empty() {
        return intervals;
    }

    // Sort by lower bound
    intervals.sort_by(|a, b| a.lo.cmp(&b.lo));

    let mut result = Vec::with_capacity(intervals.len());
    let mut current = intervals[0].clone();

    for interval in intervals.into_iter().skip(1) {
        // Check if intervals overlap or are adjacent
        if let Some(merged) = current.union(&interval) {
            current = merged;
        } else {
            result.push(current);
            current = interval;
        }
    }
    result.push(current);

    result
}

/// How many integers a single bounded component may contribute, so that a
/// component like `[0, 10^9]` costs a bounded amount of work per call rather
/// than being walked end to end.
///
/// OxiZ tuning decision: large enough to enumerate the small integer boxes
/// that dominate NIA search exhaustively, small enough that a call is cheap.
const INTEGERS_PER_COMPONENT: u32 = 400;

/// How far the ladder of small integers reaches in each direction.
///
/// OxiZ tuning decision: rays and the full real line have no endpoints for
/// [`edgewise_integers`] to work from, so this is the only stage that answers
/// them, and it has to cover the magnitudes that ordinary problems mention.
const LADDER_REACH: i64 = 96;

/// How many times a bounded component is halved by [`dyadic_interior_points`].
///
/// OxiZ tuning decision: depth `d` offers `2^(d-1)` new points per component,
/// so a modest depth already supplies far more distinct witnesses than the
/// retry allowance in `solver/resample.rs` will ever ask for.
const DYADIC_DEPTH: u32 = 4;

/// How far [`outward_along_rays`] walks past a ray's finite end.
///
/// OxiZ tuning decision: the steps double, so this reaches magnitude `2^n`
/// past the endpoint — enough to escape any bound an ordinary problem writes
/// down, at a handful of candidates.
const RAY_STRIDES: u32 = 24;

/// Integers of each bounded component, taken from its two ends inward:
/// `first`, `last`, `first + 1`, `last - 1`, and so on.
///
/// Working inward from the edges rather than sweeping left to right matters
/// when a component is wide and the cap bites: a constraint that carved this
/// component out of a larger region did so *at* these edges, so a witness
/// sitting next to one is the likeliest to also satisfy whatever neighbouring
/// constraint has not been intersected in yet.
fn edgewise_integers(set: &IntervalSet) -> impl Iterator<Item = BigRational> + '_ {
    set.bounded_components().flat_map(|(lo, hi)| {
        let first = lo.ceil();
        let last = hi.floor();
        let population = (&last - &first)
            .to_integer()
            .try_into()
            .map_or(INTEGERS_PER_COMPONENT, |width: u32| {
                width.saturating_add(1).min(INTEGERS_PER_COMPONENT)
            });
        // `first > last` means the component spans no integer at all; the
        // subtraction is then negative and the conversion above fails, so the
        // guard has to be explicit.
        let population = if first > last { 0 } else { population };
        (0..population).map(move |step| {
            let inset = BigRational::from_integer((i64::from(step) / 2).into());
            if step.is_multiple_of(2) {
                &first + inset
            } else {
                &last - inset
            }
        })
    })
}

/// Integers of growing magnitude, positive before negative: `1, -1, 2, -2, …`.
///
/// Zero is deliberately absent — [`IntervalSet::witness_candidates`] appends
/// it after the whole ladder. A witness of `0` satisfies a product constraint
/// `x·y = c` for no `y` at all, so it is the *worst* first guess for a
/// variable nothing else pins down, however "simple" it looks.
fn magnitude_ladder() -> impl Iterator<Item = BigRational> {
    (1..=LADDER_REACH)
        .flat_map(|magnitude| [magnitude, -magnitude])
        .map(|n| BigRational::from_integer(n.into()))
}

/// Dyadic points inside each bounded component, coarsest first: every
/// component's midpoint, then every component's quarter points, and so on.
///
/// This is the stage that answers a component too narrow to contain a single
/// integer — a strictly-rational band left by intersecting several
/// constraints. Going breadth-first over the depth means a set of several
/// components offers all of their midpoints before subdividing any of them.
fn dyadic_interior_points(set: &IntervalSet) -> impl Iterator<Item = BigRational> + '_ {
    (1..=DYADIC_DEPTH).flat_map(move |depth| {
        let denominator = BigRational::from_integer((1i64 << depth).into());
        set.bounded_components().flat_map(move |(lo, hi)| {
            let span = hi - lo;
            let base = lo.clone();
            let denominator = denominator.clone();
            // Odd numerators only: an even one repeats a point some coarser
            // depth already offered.
            (1..(1i64 << depth)).step_by(2).map(move |numerator| {
                &base + &span * (BigRational::from_integer(numerator.into()) / &denominator)
            })
        })
    })
}

/// Points marching away from the finite end of each half-bounded component,
/// at doubling strides: one past the end, then two, four, eight, …
///
/// A ray like `[1000, ∞)` is missed by every earlier stage — it holds no
/// bounded component and no small integer — so without this it would yield no
/// witness at all. Doubling rather than stepping by one means a retry that
/// keeps failing escapes the neighbourhood quickly instead of inching along.
fn outward_along_rays(set: &IntervalSet) -> impl Iterator<Item = BigRational> + '_ {
    set.intervals.iter().flat_map(|interval| {
        // `(origin, direction)`: where the finite end is, and which way the
        // component extends from it. A component finite on both sides is
        // covered by the integer stages and contributes nothing here.
        let anchor = match (&interval.lo, &interval.hi) {
            (Bound::Finite(lo), hi) if hi.is_pos_inf() => Some((lo.ceil(), 1i64)),
            (lo, Bound::Finite(hi)) if lo.is_neg_inf() => Some((hi.floor(), -1i64)),
            _ => None,
        };
        (0..RAY_STRIDES).filter_map(move |stride| {
            let (origin, direction) = anchor.as_ref()?;
            let step = BigRational::from_integer((direction << stride).into());
            Some(origin + step)
        })
    })
}

impl Default for IntervalSet {
    fn default() -> Self {
        Self::reals()
    }
}

impl fmt::Display for IntervalSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            write!(f, "∅")
        } else {
            for (i, interval) in self.intervals.iter().enumerate() {
                if i > 0 {
                    write!(f, " ∪ ")?;
                }
                write!(f, "{}", interval)?;
            }
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(num_bigint::BigInt::from(n))
    }

    #[test]
    fn test_interval_set_empty() {
        let set = IntervalSet::empty();
        assert!(set.is_empty());
        assert!(!set.contains(&rat(0)));
    }

    #[test]
    fn test_interval_set_reals() {
        let set = IntervalSet::reals();
        assert!(!set.is_empty());
        assert!(set.is_reals());
        assert!(set.contains(&rat(-1000)));
        assert!(set.contains(&rat(0)));
        assert!(set.contains(&rat(1000)));
    }

    #[test]
    fn test_interval_set_union() {
        let a = IntervalSet::from_interval(Interval::closed(rat(1), rat(3)));
        let b = IntervalSet::from_interval(Interval::closed(rat(5), rat(7)));
        let c = a.union(&b);

        assert_eq!(c.num_intervals(), 2);
        assert!(c.contains(&rat(2)));
        assert!(c.contains(&rat(6)));
        assert!(!c.contains(&rat(4)));
    }

    #[test]
    fn test_interval_set_union_merge() {
        let a = IntervalSet::from_interval(Interval::closed(rat(1), rat(5)));
        let b = IntervalSet::from_interval(Interval::closed(rat(3), rat(7)));
        let c = a.union(&b);

        // Should merge into [1, 7]
        assert_eq!(c.num_intervals(), 1);
        assert!(c.contains(&rat(1)));
        assert!(c.contains(&rat(7)));
    }

    /// Every point `sample_avoiding` offers must be in the set and outside
    /// `exclude`, for every stage of the candidate stream — bounded
    /// components, the magnitude ladder, dyadic interiors and rays alike.
    #[test]
    fn test_sample_avoiding_only_ever_returns_fresh_members() {
        let regions = [
            IntervalSet::from_interval(Interval::closed(rat(0), rat(3))),
            IntervalSet::reals(),
            IntervalSet::ge(rat(1000)),
            IntervalSet::le(rat(-1000)),
            IntervalSet::from_interval(Interval::open(rat(0), rat(1))),
            IntervalSet::from_interval(Interval::closed(rat(4), rat(4))),
        ];
        for region in regions {
            let mut drawn: Vec<BigRational> = Vec::new();
            while let Some(point) = region.sample_avoiding(&drawn) {
                assert!(region.contains(&point), "{point} is outside {region}");
                assert!(!drawn.contains(&point), "{point} repeated for {region}");
                drawn.push(point);
                if drawn.len() > 200 {
                    break;
                }
            }
        }
    }

    /// A variable nothing constrains must not be handed `0` as its first
    /// alternative: that is the value that makes a product equality
    /// unsatisfiable for every value of the other factor.
    #[test]
    fn test_sample_avoiding_offers_a_nonzero_integer_before_zero() {
        let reals = IntervalSet::reals();
        let point = reals
            .sample_avoiding(&[])
            .expect("the real line always has a witness");
        assert!(!point.is_zero());
        assert!(point.is_integer(), "{point} should be a small integer");
    }

    /// A ray has no bounded component and no small integer inside it, so it
    /// is answered only by the outward march past its finite end.
    #[test]
    fn test_sample_avoiding_escapes_a_far_ray() {
        let ray = IntervalSet::ge(rat(1000));
        let point = ray
            .sample_avoiding(&[])
            .expect("[1000, inf) has plenty of witnesses");
        assert!(point >= rat(1000));
        // And it keeps producing distinct ones as the search rejects them.
        let second = ray
            .sample_avoiding(std::slice::from_ref(&point))
            .expect("a ray is not exhausted by one rejection");
        assert_ne!(second, point);
        assert!(second >= rat(1000));
    }

    /// A band too narrow to hold an integer still yields witnesses, from the
    /// dyadic subdivision stage.
    #[test]
    fn test_sample_avoiding_subdivides_an_integer_free_band() {
        let band = IntervalSet::from_interval(Interval::open(rat(0), rat(1)));
        let first = band.sample_avoiding(&[]).expect("(0, 1) is not empty");
        assert!(!first.is_integer());
        assert!(first > rat(0) && first < rat(1));
        let second = band
            .sample_avoiding(std::slice::from_ref(&first))
            .expect("(0, 1) holds more than one dyadic point");
        assert_ne!(second, first);
        assert!(second > rat(0) && second < rat(1));
    }

    #[test]
    fn test_interval_set_intersect() {
        let a = IntervalSet::from_interval(Interval::closed(rat(1), rat(5)));
        let b = IntervalSet::from_interval(Interval::closed(rat(3), rat(7)));
        let c = a.intersect(&b);

        // Should be [3, 5]
        assert_eq!(c.num_intervals(), 1);
        assert!(!c.contains(&rat(2)));
        assert!(c.contains(&rat(3)));
        assert!(c.contains(&rat(5)));
        assert!(!c.contains(&rat(6)));
    }

    #[test]
    fn test_interval_set_complement() {
        let set = IntervalSet::from_interval(Interval::closed(rat(1), rat(5)));
        let comp = set.complement();

        // Complement should be (-∞, 1) ∪ (5, +∞)
        assert_eq!(comp.num_intervals(), 2);
        assert!(comp.contains(&rat(0)));
        assert!(!comp.contains(&rat(1)));
        assert!(!comp.contains(&rat(3)));
        assert!(!comp.contains(&rat(5)));
        assert!(comp.contains(&rat(6)));
    }

    #[test]
    fn test_interval_set_sample() {
        let set = IntervalSet::from_interval(Interval::closed(rat(1), rat(5)));
        let sample = set.sample();
        assert!(sample.is_some());
        let s = sample.expect("test operation should succeed");
        assert!(set.contains(&s));
    }

    #[test]
    fn test_interval_set_sign_set() {
        // Polynomial with roots at 1 and 3
        // Signs: (-∞, 1): +, (1, 3): -, (3, +∞): +
        let roots = vec![rat(1), rat(3)];
        let signs = vec![1, -1, 1];

        let positive_set = IntervalSet::sign_set(&roots, &signs, 1);
        assert!(positive_set.contains(&rat(0)));
        assert!(!positive_set.contains(&rat(2)));
        assert!(positive_set.contains(&rat(4)));

        let negative_set = IntervalSet::sign_set(&roots, &signs, -1);
        assert!(!negative_set.contains(&rat(0)));
        assert!(negative_set.contains(&rat(2)));
        assert!(!negative_set.contains(&rat(4)));

        let zero_set = IntervalSet::sign_set(&roots, &signs, 0);
        assert!(zero_set.contains(&rat(1)));
        assert!(zero_set.contains(&rat(3)));
        assert!(!zero_set.contains(&rat(2)));
    }

    #[test]
    fn test_intersect_with_roots() {
        // Interval set [0, 10]
        let set = IntervalSet::from_interval(Interval::closed(rat(0), rat(10)));

        // Roots at -1, 2, 5, 12
        let roots = vec![rat(-1), rat(2), rat(5), rat(12)];

        let intersection = set.intersect_with_roots(&roots);

        // Should contain only the roots that are in [0, 10]
        assert!(!intersection.contains(&rat(-1))); // Outside
        assert!(intersection.contains(&rat(2))); // Inside
        assert!(intersection.contains(&rat(5))); // Inside
        assert!(!intersection.contains(&rat(12))); // Outside
        assert!(!intersection.contains(&rat(3))); // Not a root
    }

    #[test]
    fn test_filter_by_sign() {
        // Interval set [0, 10]
        let set = IntervalSet::from_interval(Interval::closed(rat(0), rat(10)));

        // Polynomial with roots at 2 and 8
        // Signs: (-∞, 2): +, (2, 8): -, (8, +∞): +
        let roots = vec![rat(2), rat(8)];
        let signs = vec![1, -1, 1];

        // Filter for positive regions
        let positive = set.filter_by_sign(&roots, &signs, 1);
        assert!(positive.contains(&rat(1))); // [0, 2) ∩ [0, 10]
        assert!(!positive.contains(&rat(5))); // (2, 8) is negative
        assert!(positive.contains(&rat(9))); // (8, 10] ∩ [0, 10]

        // Filter for negative regions
        let negative = set.filter_by_sign(&roots, &signs, -1);
        assert!(!negative.contains(&rat(1)));
        assert!(negative.contains(&rat(5))); // (2, 8) ∩ [0, 10]
        assert!(!negative.contains(&rat(9)));
    }

    #[test]
    fn test_complement_point_interval() {
        // Regression test: complement of complement should be identity for point intervals
        let point = IntervalSet::from_interval(Interval::closed(rat(5), rat(5)));
        let comp = point.complement();
        let double_comp = comp.complement();

        assert!(point.contains(&rat(5)));
        assert!(!comp.contains(&rat(5)));
        assert!(double_comp.contains(&rat(5)));

        // Check equality
        assert!(point.contains(&rat(5)) == double_comp.contains(&rat(5)));
        assert!(!point.contains(&rat(4)) && !double_comp.contains(&rat(4)));
        assert!(!point.contains(&rat(6)) && !double_comp.contains(&rat(6)));
    }

    #[test]
    fn test_from_constraint() {
        // Polynomial with roots at 1 and 3
        // Signs: (-∞, 1): +, (1, 3): -, (3, +∞): +
        let roots = vec![rat(1), rat(3)];
        let signs = vec![1, -1, 1];

        // p = 0
        let eq = IntervalSet::from_constraint(&roots, &signs, ConstraintKind::Eq);
        assert!(eq.contains(&rat(1)));
        assert!(eq.contains(&rat(3)));
        assert!(!eq.contains(&rat(2)));

        // p < 0
        let lt = IntervalSet::from_constraint(&roots, &signs, ConstraintKind::Lt);
        assert!(!lt.contains(&rat(0)));
        assert!(!lt.contains(&rat(1)));
        assert!(lt.contains(&rat(2)));
        assert!(!lt.contains(&rat(3)));
        assert!(!lt.contains(&rat(4)));

        // p > 0
        let gt = IntervalSet::from_constraint(&roots, &signs, ConstraintKind::Gt);
        assert!(gt.contains(&rat(0)));
        assert!(!gt.contains(&rat(2)));
        assert!(gt.contains(&rat(4)));

        // p <= 0
        let le = IntervalSet::from_constraint(&roots, &signs, ConstraintKind::Le);
        assert!(!le.contains(&rat(0)));
        assert!(le.contains(&rat(1))); // Root included
        assert!(le.contains(&rat(2)));
        assert!(le.contains(&rat(3))); // Root included
        assert!(!le.contains(&rat(4)));

        // p >= 0
        let ge = IntervalSet::from_constraint(&roots, &signs, ConstraintKind::Ge);
        assert!(ge.contains(&rat(0)));
        assert!(ge.contains(&rat(1))); // Root included
        assert!(!ge.contains(&rat(2)));
        assert!(ge.contains(&rat(3))); // Root included
        assert!(ge.contains(&rat(4)));

        // p != 0
        let ne = IntervalSet::from_constraint(&roots, &signs, ConstraintKind::Ne);
        assert!(ne.contains(&rat(0)));
        assert!(!ne.contains(&rat(1))); // Root excluded
        assert!(ne.contains(&rat(2)));
        assert!(!ne.contains(&rat(3))); // Root excluded
        assert!(ne.contains(&rat(4)));
    }

    // Regression tests for `restrict_to_integers`: open bounds landing
    // exactly on an integer must exclude that integer, and closed bounds
    // must not admit integers outside the original range.
    #[test]
    fn test_restrict_to_integers_open_bounds_on_integer_endpoints() {
        // (1, 5) open on both ends, both endpoints are integers.
        let set = IntervalSet::from_interval(Interval::open(rat(1), rat(5)));
        let ints = set.restrict_to_integers();

        // 1 and 5 must be excluded (they were the open endpoints).
        assert!(!ints.contains(&rat(1)));
        assert!(!ints.contains(&rat(5)));
        // 2, 3, 4 must be included.
        assert!(ints.contains(&rat(2)));
        assert!(ints.contains(&rat(3)));
        assert!(ints.contains(&rat(4)));
        // Nothing outside [1, 5] should ever appear.
        assert!(!ints.contains(&rat(0)));
        assert!(!ints.contains(&rat(6)));
    }

    #[test]
    fn test_restrict_to_integers_closed_bounds_on_integer_endpoints() {
        // [1, 5] closed on both ends.
        let set = IntervalSet::from_interval(Interval::closed(rat(1), rat(5)));
        let ints = set.restrict_to_integers();

        assert!(ints.contains(&rat(1)));
        assert!(ints.contains(&rat(5)));
        assert!(ints.contains(&rat(3)));
        assert!(!ints.contains(&rat(0)));
        assert!(!ints.contains(&rat(6)));
    }

    #[test]
    fn test_restrict_to_integers_open_bounds_on_non_integer_endpoints() {
        // (1.5, 4.5) open; ceil/floor coincide with the naive formula here,
        // so this exercises the non-integer path stays correct too.
        let half = BigRational::new(num_bigint::BigInt::from(1), num_bigint::BigInt::from(2));
        let lo = rat(1) + half.clone();
        let hi = rat(4) + half;
        let set = IntervalSet::from_interval(Interval::open(lo, hi));
        let ints = set.restrict_to_integers();

        assert!(!ints.contains(&rat(1)));
        assert!(ints.contains(&rat(2)));
        assert!(ints.contains(&rat(3)));
        assert!(ints.contains(&rat(4)));
        assert!(!ints.contains(&rat(5)));
    }

    #[test]
    fn test_restrict_to_integers_half_open_at_most_at_least() {
        // (-inf, 5) open upper bound at an integer: 5 excluded, 4 included.
        let below = IntervalSet::from_interval(Interval::less_than(rat(5)));
        let ints_below = below.restrict_to_integers();
        assert!(!ints_below.contains(&rat(5)));
        assert!(ints_below.contains(&rat(4)));

        // (1, +inf) open lower bound at an integer: 1 excluded, 2 included.
        let above = IntervalSet::from_interval(Interval::greater_than(rat(1)));
        let ints_above = above.restrict_to_integers();
        assert!(!ints_above.contains(&rat(1)));
        assert!(ints_above.contains(&rat(2)));
    }

    // Property-based tests using proptest
    use proptest::prelude::*;

    proptest! {
        /// Property: Union is commutative
        #[test]
        fn prop_union_commutative(a in -1000i64..1000, b in -1000i64..1000,
                                   c in -1000i64..1000, d in -1000i64..1000) {
            let (lo_a, hi_a) = if a <= b { (a, b) } else { (b, a) };
            let (lo_c, hi_c) = if c <= d { (c, d) } else { (d, c) };

            let set1 = IntervalSet::from_interval(Interval::closed(rat(lo_a), rat(hi_a)));
            let set2 = IntervalSet::from_interval(Interval::closed(rat(lo_c), rat(hi_c)));

            let union1 = set1.union(&set2);
            let union2 = set2.union(&set1);

            // Check that both unions contain the same elements
            let mid_ab = (lo_a + hi_a) / 2;
            let mid_cd = (lo_c + hi_c) / 2;
            for x in [lo_a-1, lo_a, mid_ab, hi_a, lo_c-1, lo_c, mid_cd, hi_c, hi_c+1].iter() {
                prop_assert_eq!(union1.contains(&rat(*x)), union2.contains(&rat(*x)));
            }
        }

        /// Property: Intersection is commutative
        #[test]
        fn prop_intersect_commutative(a in -1000i64..1000, b in -1000i64..1000,
                                       c in -1000i64..1000, d in -1000i64..1000) {
            let (lo_a, hi_a) = if a <= b { (a, b) } else { (b, a) };
            let (lo_c, hi_c) = if c <= d { (c, d) } else { (d, c) };

            let set1 = IntervalSet::from_interval(Interval::closed(rat(lo_a), rat(hi_a)));
            let set2 = IntervalSet::from_interval(Interval::closed(rat(lo_c), rat(hi_c)));

            let inter1 = set1.intersect(&set2);
            let inter2 = set2.intersect(&set1);

            // Check that both intersections contain the same elements
            let mid_ab = (lo_a + hi_a) / 2;
            let mid_cd = (lo_c + hi_c) / 2;
            for x in [lo_a-1, lo_a, mid_ab, hi_a, lo_c-1, lo_c, mid_cd, hi_c, hi_c+1].iter() {
                prop_assert_eq!(inter1.contains(&rat(*x)), inter2.contains(&rat(*x)));
            }
        }

        /// Property: Complement of complement is identity
        #[test]
        fn prop_complement_involutive(a in -1000i64..1000, b in -1000i64..1000) {
            let (lo, hi) = if a <= b { (a, b) } else { (b, a) };

            let set = IntervalSet::from_interval(Interval::closed(rat(lo), rat(hi)));
            let double_complement = set.complement().complement();

            // Check points within and at boundaries
            let mid = (lo + hi) / 2;
            for x in [lo, mid, hi].iter() {
                prop_assert_eq!(set.contains(&rat(*x)), double_complement.contains(&rat(*x)),
                    "Failed at x={}, set.contains={}, double_complement.contains={}",
                    x, set.contains(&rat(*x)), double_complement.contains(&rat(*x)));
            }
        }

        /// Property: Union with empty set is identity
        #[test]
        fn prop_union_empty_identity(a in -1000i64..1000, b in -1000i64..1000) {
            let (lo, hi) = if a <= b { (a, b) } else { (b, a) };

            let set = IntervalSet::from_interval(Interval::closed(rat(lo), rat(hi)));
            let empty = IntervalSet::empty();
            let result = set.union(&empty);

            let mid = (lo + hi) / 2;
            for x in [lo, mid, hi].iter() {
                prop_assert_eq!(set.contains(&rat(*x)), result.contains(&rat(*x)));
            }
        }

        /// Property: Intersection with empty set is empty
        #[test]
        fn prop_intersect_empty(a in -1000i64..1000, b in -1000i64..1000) {
            let (lo, hi) = if a <= b { (a, b) } else { (b, a) };

            let set = IntervalSet::from_interval(Interval::closed(rat(lo), rat(hi)));
            let empty = IntervalSet::empty();
            let result = set.intersect(&empty);

            prop_assert!(result.is_empty());
        }

        /// Property: De Morgan's law for intersection
        #[test]
        fn prop_demorgan_intersect(a in -1000i64..1000, b in -1000i64..1000,
                                     c in -1000i64..1000, d in -1000i64..1000) {
            let (lo_a, hi_a) = if a <= b { (a, b) } else { (b, a) };
            let (lo_c, hi_c) = if c <= d { (c, d) } else { (d, c) };

            let set1 = IntervalSet::from_interval(Interval::closed(rat(lo_a), rat(hi_a)));
            let set2 = IntervalSet::from_interval(Interval::closed(rat(lo_c), rat(hi_c)));

            // complement(A ∩ B) = complement(A) ∪ complement(B)
            let left = set1.intersect(&set2).complement();
            let right = set1.complement().union(&set2.complement());

            // Check several points
            let mid_ab = (lo_a + hi_a) / 2;
            let mid_cd = (lo_c + hi_c) / 2;
            for x in [lo_a-1, lo_a, mid_ab, hi_a, lo_c-1, lo_c, mid_cd, hi_c, hi_c+1].iter() {
                prop_assert_eq!(left.contains(&rat(*x)), right.contains(&rat(*x)));
            }
        }

        /// Property: Intersection is subset of both operands
        #[test]
        fn prop_intersect_subset(a in -1000i64..1000, b in -1000i64..1000,
                                  c in -1000i64..1000, d in -1000i64..1000,
                                  x in -2000i64..2000) {
            let (lo_a, hi_a) = if a <= b { (a, b) } else { (b, a) };
            let (lo_c, hi_c) = if c <= d { (c, d) } else { (d, c) };

            let set1 = IntervalSet::from_interval(Interval::closed(rat(lo_a), rat(hi_a)));
            let set2 = IntervalSet::from_interval(Interval::closed(rat(lo_c), rat(hi_c)));
            let inter = set1.intersect(&set2);

            let point = rat(x);
            // If x is in intersection, it must be in both sets
            if inter.contains(&point) {
                prop_assert!(set1.contains(&point));
                prop_assert!(set2.contains(&point));
            }
        }

        /// Property: Union contains both operands
        #[test]
        fn prop_union_superset(a in -1000i64..1000, b in -1000i64..1000,
                                c in -1000i64..1000, d in -1000i64..1000,
                                x in -2000i64..2000) {
            let (lo_a, hi_a) = if a <= b { (a, b) } else { (b, a) };
            let (lo_c, hi_c) = if c <= d { (c, d) } else { (d, c) };

            let set1 = IntervalSet::from_interval(Interval::closed(rat(lo_a), rat(hi_a)));
            let set2 = IntervalSet::from_interval(Interval::closed(rat(lo_c), rat(hi_c)));
            let union = set1.union(&set2);

            let point = rat(x);
            // If x is in either set, it must be in union
            if set1.contains(&point) || set2.contains(&point) {
                prop_assert!(union.contains(&point));
            }
        }
    }
}
