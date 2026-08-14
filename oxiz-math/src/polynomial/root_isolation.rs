//! Root Isolation for Univariate Polynomials.
//!
//! Implements algorithms for isolating real roots of polynomials including:
//! - Sturm sequences
//! - Descartes' rule of signs
//! - Continued fraction method
//! - Bisection refinement

#[allow(unused_imports)]
use crate::prelude::*;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;

/// Safety-net bisection-depth ceiling for [`RootIsolator::isolate_roots`]'s
/// bisection search (`bisect_and_isolate`).
///
/// Independent of [`RootIsolator`]'s `max_iterations` field, which bounds a
/// different loop: the *refinement* of an already-isolated single-root
/// interval in [`RootIsolator::refine_root_interval`], not the isolation
/// search itself. See [`IsolationStats::incomplete`] for why this is a pure
/// safety net rather than a correctness-affecting parameter, and
/// `crate::algebraic::isolate`'s sibling implementation of the same
/// algorithm (or `oxiz-nlsat`'s `SturmSequence::isolate_in_interval_bounded`,
/// same algorithm again over a different `Polynomial` type) for the same
/// defensive pattern applied elsewhere in this workspace.
const MAX_ROOT_ISOLATION_DEPTH: u32 = 4096;

/// Root isolation engine for real polynomials.
pub struct RootIsolator {
    /// Precision threshold for root refinement
    precision: BigRational,
    /// Maximum refinement iterations
    max_iterations: usize,
    /// Statistics
    stats: IsolationStats,
}

/// Isolated root interval.
#[derive(Debug, Clone)]
pub struct RootInterval {
    /// Left endpoint
    pub left: BigRational,
    /// Right endpoint
    pub right: BigRational,
    /// Is left endpoint included
    pub left_closed: bool,
    /// Is right endpoint included
    pub right_closed: bool,
    /// Number of roots in this interval
    pub multiplicity: usize,
}

/// Root isolation statistics.
#[derive(Debug, Clone, Default)]
pub struct IsolationStats {
    /// Number of Sturm sequence evaluations
    pub sturm_evaluations: usize,
    /// Number of Descartes tests
    pub descartes_tests: usize,
    /// Number of bisection steps
    pub bisection_steps: usize,
    /// Total intervals generated
    pub intervals_generated: usize,
    /// Set to `true` if the bisection search ever hit
    /// `MAX_ROOT_ISOLATION_DEPTH` before narrowing a sub-interval down to
    /// exactly one root.
    ///
    /// With a correct Sturm sequence and exact rational bisection this
    /// should never happen for any well-formed polynomial: distinct real
    /// roots always have a positive minimum pairwise separation, so repeated
    /// bisection is mathematically guaranteed to isolate each one
    /// eventually. A `true` value indicates a pathological input or an
    /// upstream bug, and it also means [`RootIsolator::isolate_roots`]'s
    /// returned list may be missing one or more roots for the affected
    /// sub-interval -- this flag makes that condition visible instead of it
    /// being a silently-incomplete result.
    pub incomplete: bool,
}

/// One pending sub-interval in [`RootIsolator::bisect_and_isolate`]'s
/// explicit work-stack, carrying the sign-variation counts already known
/// for its endpoints and its remaining bisection-depth budget.
struct BisectItem {
    /// Lower endpoint.
    lo: BigRational,
    /// Upper endpoint.
    hi: BigRational,
    /// Sign-variation count at `lo`.
    lo_vars: usize,
    /// Sign-variation count at `hi`.
    hi_vars: usize,
    /// Remaining bisection-depth budget (see [`MAX_ROOT_ISOLATION_DEPTH`]).
    depth: u32,
}

impl RootIsolator {
    /// Create a new root isolator.
    pub fn new(precision: BigRational) -> Self {
        Self {
            precision,
            max_iterations: 1000,
            stats: IsolationStats::default(),
        }
    }

    /// Isolate all real roots of a polynomial in an interval.
    pub fn isolate_roots(
        &mut self,
        poly: &[BigRational],
        interval: (BigRational, BigRational),
    ) -> Vec<RootInterval> {
        self.isolate_roots_bounded(poly, interval, MAX_ROOT_ISOLATION_DEPTH)
    }

    /// [`Self::isolate_roots`] with an explicit bisection-depth ceiling, so
    /// tests can force the [`IsolationStats::incomplete`] path
    /// deterministically without needing a pathological polynomial that
    /// requires thousands of bisection levels.
    fn isolate_roots_bounded(
        &mut self,
        poly: &[BigRational],
        interval: (BigRational, BigRational),
        max_depth: u32,
    ) -> Vec<RootInterval> {
        // Remove leading zeros
        let poly = Self::normalize_polynomial(poly);

        if poly.len() <= 1 {
            return vec![];
        }

        // Build Sturm sequence
        let sturm_seq = self.build_sturm_sequence(&poly);

        // Count sign variations at endpoints. Normalize a reversed/degenerate
        // interval (`left > right`) up front rather than let a Sturm
        // sign-variation count for the (higher-x) `left` come out smaller
        // than for `right` – sign variations are non-increasing as x
        // increases, so a reversed pair would otherwise underflow the
        // `usize` subtraction below.
        let (left, right) = interval;
        let (left, right) = if left <= right {
            (left, right)
        } else {
            (right, left)
        };
        let left_variations = self.count_sign_variations(&sturm_seq, &left);
        let right_variations = self.count_sign_variations(&sturm_seq, &right);
        self.stats.sturm_evaluations += 2;

        // Defense in depth: even for a well-ordered interval, use a
        // saturating subtraction so a degenerate/edge-case count (e.g. an
        // interval collapsing to a point) can never panic.
        let num_roots = left_variations.saturating_sub(right_variations);

        if num_roots == 0 {
            return vec![];
        } else if num_roots == 1 {
            // Single root - refine to desired precision
            let refined = self.refine_root_interval(&poly, left, right);
            return vec![refined];
        }

        // Multiple roots - bisect
        self.bisect_and_isolate(
            &poly,
            &sturm_seq,
            BisectItem {
                lo: left,
                hi: right,
                lo_vars: left_variations,
                hi_vars: right_variations,
                depth: max_depth,
            },
        )
    }

    /// Build Sturm sequence for a polynomial.
    fn build_sturm_sequence(&self, poly: &[BigRational]) -> Vec<Vec<BigRational>> {
        let mut sequence = Vec::new();

        // f_0 = f(x)
        sequence.push(poly.to_vec());

        // f_1 = f'(x)
        let derivative = Self::derivative(poly);
        if derivative.is_empty() {
            return sequence;
        }
        sequence.push(derivative);

        // f_{i+1} = -remainder(f_{i-1}, f_i)
        loop {
            let len = sequence.len();
            let f_prev = &sequence[len - 2];
            let f_curr = &sequence[len - 1];

            let remainder = Self::polynomial_remainder(f_prev, f_curr);

            if remainder.is_empty() || Self::is_zero_poly(&remainder) {
                break;
            }

            // Negate remainder
            let neg_remainder: Vec<BigRational> = remainder.iter().map(|c| -c.clone()).collect();

            sequence.push(neg_remainder);
        }

        sequence
    }

    /// Count sign variations in a Sturm sequence at a point.
    fn count_sign_variations(&self, sturm_seq: &[Vec<BigRational>], x: &BigRational) -> usize {
        let mut signs = Vec::new();

        for poly in sturm_seq {
            let value = Self::evaluate(poly, x);
            if !value.is_zero() {
                signs.push(value > BigRational::zero());
            }
        }

        // Count sign changes
        let mut variations = 0;
        for i in 0..signs.len().saturating_sub(1) {
            if signs[i] != signs[i + 1] {
                variations += 1;
            }
        }

        variations
    }

    /// Bisect an interval and isolate the roots within it.
    ///
    /// Iterative (explicit work-stack), not mutually recursive with
    /// [`Self::isolate_roots`], with `initial.depth` as a defensive
    /// bisection-depth ceiling (see [`IsolationStats::incomplete`] for why
    /// this should never actually bind for a well-formed polynomial). Each
    /// work item carries the sign-variation counts already known for its
    /// endpoints -- inherited from the bisection that produced it, or from
    /// the caller for the initial item -- so no endpoint is ever
    /// re-evaluated. The original mutual recursion re-built the Sturm
    /// sequence and re-evaluated shared endpoints at every level instead;
    /// the isolated intervals returned here are identical, this just does
    /// not repeat work to get them.
    fn bisect_and_isolate(
        &mut self,
        poly: &[BigRational],
        sturm_seq: &[Vec<BigRational>],
        initial: BisectItem,
    ) -> Vec<RootInterval> {
        let mut intervals = Vec::new();
        let mut work = vec![initial];

        while let Some(BisectItem {
            lo,
            hi,
            lo_vars,
            hi_vars,
            depth,
        }) = work.pop()
        {
            let num_roots = lo_vars.saturating_sub(hi_vars);

            if num_roots == 0 {
                continue;
            }
            if num_roots == 1 {
                intervals.push(self.refine_root_interval(poly, lo, hi));
                continue;
            }
            if depth == 0 {
                // Defensive-only fallback (see `IsolationStats::incomplete`):
                // dropping this sub-range rather than recursing forever or
                // fabricating a single interval that falsely claims to
                // isolate multiple roots. Recorded so callers can detect it.
                self.stats.incomplete = true;
                continue;
            }

            self.stats.bisection_steps += 1;
            let mid = (&lo + &hi) / BigRational::from_integer(BigInt::from(2));
            let mid_vars = self.count_sign_variations(sturm_seq, &mid);
            self.stats.sturm_evaluations += 1;

            let left_roots = lo_vars.saturating_sub(mid_vars);
            let right_roots = mid_vars.saturating_sub(hi_vars);

            // Push right first so left (pushed last) pops first and its
            // whole subtree -- including everything it in turn pushes -- is
            // drained before right is touched, matching the original
            // recursion's left-to-right result order.
            if right_roots > 0 {
                work.push(BisectItem {
                    lo: mid.clone(),
                    hi,
                    lo_vars: mid_vars,
                    hi_vars,
                    depth: depth - 1,
                });
            }
            if left_roots > 0 {
                work.push(BisectItem {
                    lo,
                    hi: mid,
                    lo_vars,
                    hi_vars: mid_vars,
                    depth: depth - 1,
                });
            }
        }

        intervals
    }

    /// Refine a root interval to desired precision.
    fn refine_root_interval(
        &mut self,
        poly: &[BigRational],
        mut left: BigRational,
        mut right: BigRational,
    ) -> RootInterval {
        let mut iterations = 0;

        while &right - &left > self.precision && iterations < self.max_iterations {
            let mid = (&left + &right) / BigRational::from_integer(BigInt::from(2));
            let mid_val = Self::evaluate(poly, &mid);

            if mid_val.is_zero() {
                return RootInterval {
                    left: mid.clone(),
                    right: mid,
                    left_closed: true,
                    right_closed: true,
                    multiplicity: 1,
                };
            }

            let left_val = Self::evaluate(poly, &left);

            if (left_val > BigRational::zero()) == (mid_val > BigRational::zero()) {
                left = mid;
            } else {
                right = mid;
            }

            iterations += 1;
        }

        self.stats.intervals_generated += 1;

        RootInterval {
            left,
            right,
            left_closed: false,
            right_closed: false,
            multiplicity: 1,
        }
    }

    /// Evaluate polynomial at a point using Horner's method.
    fn evaluate(poly: &[BigRational], x: &BigRational) -> BigRational {
        if poly.is_empty() {
            return BigRational::zero();
        }

        let mut result = poly[0].clone();
        for coeff in &poly[1..] {
            result = result * x + coeff;
        }
        result
    }

    /// Compute polynomial derivative.
    fn derivative(poly: &[BigRational]) -> Vec<BigRational> {
        if poly.len() <= 1 {
            return vec![];
        }

        let mut deriv = Vec::with_capacity(poly.len() - 1);
        for (i, coeff) in poly.iter().enumerate().take(poly.len() - 1) {
            let degree = (poly.len() - 1 - i) as i64;
            deriv.push(coeff * BigRational::from_integer(BigInt::from(degree)));
        }
        deriv
    }

    /// Polynomial division - compute remainder.
    fn polynomial_remainder(dividend: &[BigRational], divisor: &[BigRational]) -> Vec<BigRational> {
        if divisor.is_empty() || Self::is_zero_poly(divisor) {
            return vec![];
        }

        let mut remainder = dividend.to_vec();

        while remainder.len() >= divisor.len() && !Self::is_zero_poly(&remainder) {
            let lead_div = &divisor[0];
            let lead_rem = &remainder[0];

            if lead_div.is_zero() {
                break;
            }

            let quotient_coeff = lead_rem / lead_div;

            for i in 0..divisor.len() {
                remainder[i] = &remainder[i] - &quotient_coeff * &divisor[i];
            }

            remainder.remove(0);
        }

        remainder
    }

    /// Normalize polynomial by removing leading zeros.
    fn normalize_polynomial(poly: &[BigRational]) -> Vec<BigRational> {
        let mut result = poly.to_vec();
        while !result.is_empty() && result[0].is_zero() {
            result.remove(0);
        }
        result
    }

    /// Check if polynomial is zero.
    fn is_zero_poly(poly: &[BigRational]) -> bool {
        poly.iter().all(|c| c.is_zero())
    }

    /// Get statistics.
    pub fn stats(&self) -> &IsolationStats {
        &self.stats
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::{One, Zero};

    #[test]
    fn test_root_isolator() {
        let precision = BigRational::new(BigInt::from(1), BigInt::from(1000));
        let isolator = RootIsolator::new(precision);

        assert_eq!(isolator.stats.sturm_evaluations, 0);
    }

    #[test]
    fn test_sturm_sequence() {
        let precision = BigRational::new(BigInt::from(1), BigInt::from(100));
        let isolator = RootIsolator::new(precision);

        // f(x) = x^2 - 2
        let poly = vec![
            BigRational::one(),
            BigRational::zero(),
            BigRational::from_integer(BigInt::from(-2)),
        ];

        let sturm = isolator.build_sturm_sequence(&poly);
        assert!(!sturm.is_empty());
    }

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(n))
    }

    // ========  ========
    // `bisect_and_isolate` bisection-depth regression tests (audit: no
    // bound at all on the bisection recursion; `oxiz-nlsat`'s sibling
    // implementation of the same algorithm already carries a 4096-level
    // safety net).
    // ========  ========

    #[test]
    fn test_isolate_roots_multiple_roots_via_bisection_behaviour_preserved() {
        // f(x) = x^2 - 2 (descending coeffs), two real roots (+-sqrt(2)):
        // isolate_roots must bisect a wide bracketing interval to separate
        // them. This exact path (num_roots > 1) had no prior test coverage
        // in this file.
        let poly = vec![rat(1), rat(0), rat(-2)];
        let precision = BigRational::new(BigInt::from(1), BigInt::from(1_000_000));
        let mut isolator = RootIsolator::new(precision);

        let intervals = isolator.isolate_roots(&poly, (rat(-10), rat(10)));

        assert_eq!(intervals.len(), 2, "x^2 - 2 has exactly two real roots");
        for iv in &intervals {
            assert!(iv.left <= iv.right);
        }
        assert!(
            intervals[0].right <= intervals[1].left || intervals[1].right <= intervals[0].left,
            "isolating intervals must not overlap: {:?}",
            intervals
        );
        assert!(
            !isolator.stats().incomplete,
            "a normal, well-separated polynomial must never hit the depth cap"
        );
    }

    #[test]
    fn test_isolate_roots_bounded_depth_cap_is_visible_not_silent() {
        // f(x) = x^3 - x = x(x-1)(x+1), three real roots. With a bisection
        // budget too small to separate all three, the search must stop and
        // record `stats.incomplete = true` -- never hang, never fabricate a
        // merged interval that falsely claims to isolate multiple roots.
        let poly = vec![rat(1), rat(0), rat(-1), rat(0)];
        let precision = BigRational::new(BigInt::from(1), BigInt::from(1_000_000));
        let mut isolator = RootIsolator::new(precision);

        let results = isolator.isolate_roots_bounded(&poly, (rat(-10), rat(10)), 1);

        assert!(
            isolator.stats().incomplete,
            "an insufficient depth budget must be recorded as incomplete"
        );
        assert!(
            results.len() < 3,
            "a truncated search must not fabricate all three roots, got {results:?}"
        );
    }

    #[test]
    fn test_isolate_roots_bounded_sufficient_depth_never_marks_incomplete() {
        // The same cubic through the public API (default
        // MAX_ROOT_ISOLATION_DEPTH) must isolate all three roots and never
        // set `incomplete`.
        let poly = vec![rat(1), rat(0), rat(-1), rat(0)];
        let precision = BigRational::new(BigInt::from(1), BigInt::from(1_000_000));
        let mut isolator = RootIsolator::new(precision);

        let intervals = isolator.isolate_roots(&poly, (rat(-10), rat(10)));

        assert_eq!(intervals.len(), 3);
        assert!(!isolator.stats().incomplete);
    }

    #[test]
    fn test_isolate_roots_deep_bisection_small_stack() {
        // Two real roots 2^-2000 apart force many bisection levels (well
        // under MAX_ROOT_ISOLATION_DEPTH, so this is a *deep-but-finite*
        // case, not the depth-cap path) from inside a thread with a
        // deliberately small (1 MiB) stack. A stack overflow aborts the
        // whole process, so "the thread returned at all" is itself part of
        // the assertion.
        let handle = std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(|| {
                let mut den = BigInt::from(1u32);
                for _ in 0..2000 {
                    den *= 2;
                }
                let eps = BigRational::new(BigInt::from(1), den);
                // f(x) = x*(x - eps) = x^2 - eps*x (descending coeffs)
                let poly = vec![rat(1), -eps, rat(0)];
                // Precision only bounds the post-isolation refinement step
                // (via `max_iterations`, itself already bounded), not the
                // isolation/bisection search depth being tested here, so a
                // modest value is enough.
                let precision = BigRational::new(BigInt::from(1), BigInt::from(1_000_000));
                let mut isolator = RootIsolator::new(precision);
                let intervals = isolator.isolate_roots(&poly, (rat(-1), rat(1)));
                assert_eq!(intervals.len(), 2);
                assert!(!isolator.stats().incomplete);
            })
            .expect("spawning a thread with an explicit stack size must succeed");
        handle
            .join()
            .expect("a deep-but-finite bisection must not overflow a 1 MiB stack");
    }
}
