//! Root Isolation for Algebraic Numbers.
//!
//! Algorithms for isolating real roots of polynomials into disjoint intervals.
//! Each interval contains exactly one root, enabling construction of algebraic numbers.
//!
//! ## Algorithms
//!
//! - **Sturm Sequences**: Count roots in intervals
//! - **Bisection**: Refine intervals containing roots
//! - **Descartes' Rule**: Upper bound on positive roots
//!
//! ## References
//!
//! - "Algorithms in Real Algebraic Geometry" (Basu et al., 2006)
//! - Z3's `math/polynomial/algebraic_numbers.cpp`

use crate::polynomial::root_counting::Polynomial;
#[allow(unused_imports)]
use crate::prelude::*;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

/// Isolating interval for a root.
#[derive(Debug, Clone)]
pub struct IsolatingInterval {
    /// Lower bound.
    pub lower: BigRational,
    /// Upper bound.
    pub upper: BigRational,
    /// Sign at lower bound.
    pub sign_lower: i32,
    /// Sign at upper bound.
    pub sign_upper: i32,
}

impl IsolatingInterval {
    /// Create a new isolating interval.
    pub fn new(lower: BigRational, upper: BigRational, sign_lower: i32, sign_upper: i32) -> Self {
        Self {
            lower,
            upper,
            sign_lower,
            sign_upper,
        }
    }

    /// Get interval width.
    pub fn width(&self) -> BigRational {
        &self.upper - &self.lower
    }

    /// Get midpoint.
    pub fn midpoint(&self) -> BigRational {
        (&self.lower + &self.upper) / BigRational::from(BigInt::from(2))
    }
}

/// Safety-net bisection-depth ceiling for [`RootIsolator::isolate_in_interval`].
///
/// This is independent of [`IsolationConfig::max_iterations`] (which bounds
/// the *refinement* of an already-isolated single-root interval, not the
/// isolation search itself). See [`IsolationStats::incomplete`] for why this
/// is a pure safety net rather than a correctness-affecting parameter.
const MAX_ROOT_ISOLATION_DEPTH: u32 = 4096;

/// Configuration for root isolation.
#[derive(Debug, Clone)]
pub struct IsolationConfig {
    /// Use Sturm sequences for root counting.
    pub use_sturm: bool,
    /// Use Descartes' rule for optimization.
    pub use_descartes: bool,
    /// Maximum refinement iterations.
    pub max_iterations: usize,
    /// Precision threshold.
    pub precision: BigRational,
}

impl Default for IsolationConfig {
    fn default() -> Self {
        Self {
            use_sturm: true,
            use_descartes: true,
            max_iterations: 1000,
            precision: BigRational::new(BigInt::from(1), BigInt::from(1_000_000)),
        }
    }
}

/// Statistics for root isolation.
#[derive(Debug, Clone, Default)]
pub struct IsolationStats {
    /// Sturm sequence computations.
    pub sturm_computations: u64,
    /// Bisection steps.
    pub bisection_steps: u64,
    /// Sign evaluations.
    pub sign_evaluations: u64,
    /// Roots isolated.
    pub roots_isolated: u64,
    /// Set to `true` if bisection ever hit `MAX_ROOT_ISOLATION_DEPTH`
    /// before narrowing a sub-interval down to exactly one root.
    ///
    /// With a correct Sturm sequence and exact rational bisection this
    /// should never happen for any well-formed polynomial: distinct real
    /// roots always have a positive minimum pairwise separation, so repeated
    /// bisection is mathematically guaranteed to isolate each one eventually.
    /// A `true` value therefore indicates a pathological input or an
    /// upstream bug (e.g. an incorrect Sturm sequence), and it also means
    /// [`RootIsolator::isolate_roots`]'s returned list may be missing one or
    /// more roots for the affected sub-interval -- this flag is what makes
    /// that condition visible instead of it being a silently-incomplete
    /// result.
    pub incomplete: bool,
}

/// Interval refinement method.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntervalRefinement {
    /// Bisection method.
    Bisection,
    /// Newton's method.
    Newton,
    /// Hybrid (bisection + Newton).
    Hybrid,
}

/// Root isolator using interval arithmetic.
pub struct RootIsolator {
    /// Polynomial to isolate roots for (univariate over Q).
    poly: Polynomial,
    /// Configuration.
    config: IsolationConfig,
    /// Statistics.
    stats: IsolationStats,
    /// Cached Sturm sequence.
    sturm_sequence: Option<Vec<Polynomial>>,
}

impl RootIsolator {
    /// Create a new root isolator.
    pub fn new(poly: Polynomial, config: IsolationConfig) -> Self {
        Self {
            poly,
            config,
            stats: IsolationStats::default(),
            sturm_sequence: None,
        }
    }

    /// Create with default configuration.
    pub fn default_config(poly: Polynomial) -> Self {
        Self::new(poly, IsolationConfig::default())
    }

    /// Isolate all real roots of the polynomial.
    pub fn isolate_roots(&mut self) -> Vec<IsolatingInterval> {
        // Handle trivial cases: zero polynomial or non-zero constant
        let is_zero = self.poly.degree() == 0 && self.poly.coeffs.first().is_none_or(Zero::is_zero);
        if is_zero || self.poly.degree() == 0 {
            return Vec::new();
        }

        // Compute Sturm sequence if enabled
        if self.config.use_sturm {
            self.compute_sturm_sequence();
        }

        // Find bounds for all real roots
        let (lower_bound, upper_bound) = self.root_bounds();

        // Isolate roots in [lower_bound, upper_bound]
        self.isolate_in_interval(lower_bound, upper_bound)
    }

    /// Compute Sturm sequence for the polynomial.
    fn compute_sturm_sequence(&mut self) {
        let mut seq = vec![self.poly.clone(), self.poly.derivative()];

        loop {
            let len = seq.len();
            if len < 2 {
                break;
            }

            let last = &seq[len - 1];
            // Stop when the tail is degree-0 (zero or non-zero constant): any polynomial
            // mod a constant is 0, so the next negated remainder would be 0 anyway.
            if last.degree() == 0 {
                break;
            }

            let remainder = seq[len - 2].remainder(&seq[len - 1]);

            // Negate remainder (Sturm sequence convention: p_{k+1} = -rem(p_{k-1}, p_k))
            let negated = Polynomial::new(remainder.coeffs.iter().map(|c| -c).collect());

            if negated.degree() == 0 && negated.coeffs.first().is_none_or(Zero::is_zero) {
                break;
            }

            seq.push(negated);

            // Guard against degenerate polynomials
            if seq.len() > 1000 {
                break;
            }
        }

        self.sturm_sequence = Some(seq);
        self.stats.sturm_computations += 1;
    }

    /// Count roots in an interval using Sturm's theorem.
    fn count_roots(&mut self, lower: &BigRational, upper: &BigRational) -> usize {
        if self.sturm_sequence.is_none() {
            self.compute_sturm_sequence();
        }

        // Clone to avoid simultaneous immutable+mutable borrow of self.
        let seq: Vec<Polynomial> = self.sturm_sequence.as_ref().cloned().unwrap_or_default();

        let sign_changes_lower = self.count_sign_changes(&seq, lower);
        let sign_changes_upper = self.count_sign_changes(&seq, upper);

        (sign_changes_lower as isize - sign_changes_upper as isize).unsigned_abs()
    }

    /// Count sign changes in Sturm sequence at a point.
    fn count_sign_changes(&mut self, seq: &[Polynomial], point: &BigRational) -> usize {
        self.stats.sign_evaluations += seq.len() as u64;

        let signs: Vec<i32> = seq
            .iter()
            .map(|p| {
                let val = p.eval(point);
                if val.is_positive() {
                    1
                } else if val.is_negative() {
                    -1
                } else {
                    0
                }
            })
            .filter(|&s| s != 0) // Skip zeros per Sturm's theorem
            .collect();

        // Count sign changes
        let mut changes = 0;
        for i in 0..signs.len().saturating_sub(1) {
            if signs[i] != signs[i + 1] {
                changes += 1;
            }
        }

        changes
    }

    /// Compute bounds containing all real roots (Cauchy bound).
    ///
    /// Cauchy bound: |roots| <= 1 + max(|a_i| / |a_n|)
    pub(crate) fn root_bounds(&self) -> (BigRational, BigRational) {
        let coeffs = &self.poly.coeffs;
        if coeffs.is_empty() {
            return (BigRational::zero(), BigRational::zero());
        }

        let leading = match coeffs.last() {
            Some(c) => c.abs(),
            None => return (BigRational::zero(), BigRational::zero()),
        };

        if leading.is_zero() {
            return (BigRational::zero(), BigRational::zero());
        }

        let mut max_ratio = BigRational::zero();
        for coeff in coeffs.iter().take(coeffs.len() - 1) {
            let ratio = coeff.abs() / &leading;
            if ratio > max_ratio {
                max_ratio = ratio;
            }
        }

        let bound = BigRational::from(BigInt::from(1)) + max_ratio;

        (-bound.clone(), bound)
    }

    /// Isolate roots in a given interval.
    ///
    /// Iterative (explicit work-stack) rather than recursive, with
    /// [`MAX_ROOT_ISOLATION_DEPTH`] as a defensive bisection-depth ceiling:
    /// see [`IsolationStats::incomplete`] for why this bound should never
    /// actually be hit for a well-formed polynomial, and
    /// [`crate::polynomial::root_isolation`]'s sibling implementation of the
    /// same algorithm, or `oxiz-nlsat`'s `SturmSequence::isolate_in_interval_bounded`
    /// (same algorithm again, over a different `Polynomial` type), for the
    /// same defensive pattern applied elsewhere in this workspace.
    fn isolate_in_interval(
        &mut self,
        lower: BigRational,
        upper: BigRational,
    ) -> Vec<IsolatingInterval> {
        self.isolate_in_interval_bounded(lower, upper, MAX_ROOT_ISOLATION_DEPTH)
    }

    /// [`Self::isolate_in_interval`] with an explicit depth ceiling, so
    /// tests can force the [`IsolationStats::incomplete`] path
    /// deterministically without needing a pathological polynomial that
    /// requires thousands of bisection levels.
    fn isolate_in_interval_bounded(
        &mut self,
        lower: BigRational,
        upper: BigRational,
        max_depth: u32,
    ) -> Vec<IsolatingInterval> {
        let mut results = Vec::new();
        // Each work item is a sub-interval still to resolve, paired with
        // its remaining bisection-depth budget (decremented per level, like
        // a recursion-depth parameter would be, but living on the heap
        // instead of the native call stack).
        let mut work: Vec<(BigRational, BigRational, u32)> = vec![(lower, upper, max_depth)];

        while let Some((lo, hi, depth)) = work.pop() {
            let num_roots = self.count_roots(&lo, &hi);

            if num_roots == 0 {
                continue;
            }

            if num_roots == 1 {
                // Single root in interval
                let sign_lower = self.eval_sign(&lo);
                let sign_upper = self.eval_sign(&hi);

                self.stats.roots_isolated += 1;

                results.push(IsolatingInterval::new(lo, hi, sign_lower, sign_upper));
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

            // Multiple roots: bisect. Push the right half first so the
            // left half (pushed last) is popped -- and fully drained,
            // including everything it in turn pushes -- before the right
            // half is touched, reproducing the original recursion's
            // left-to-right result order.
            self.stats.bisection_steps += 1;

            let mid = (&lo + &hi) / BigRational::from(BigInt::from(2));
            work.push((mid.clone(), hi, depth - 1));
            work.push((lo, mid, depth - 1));
        }

        results
    }

    /// Evaluate sign of polynomial at a point (-1, 0, or 1).
    fn eval_sign(&mut self, point: &BigRational) -> i32 {
        self.stats.sign_evaluations += 1;

        let val = self.poly.eval(point);

        if val.is_positive() {
            1
        } else if val.is_negative() {
            -1
        } else {
            0
        }
    }

    /// Refine an isolating interval.
    pub fn refine_interval(
        &mut self,
        interval: &IsolatingInterval,
        method: IntervalRefinement,
    ) -> IsolatingInterval {
        match method {
            IntervalRefinement::Bisection => self.refine_bisection(interval),
            IntervalRefinement::Newton => self.refine_newton(interval),
            IntervalRefinement::Hybrid => {
                // Try Newton first, fall back to bisection if not contracting fast enough
                let newton_result = self.refine_newton(interval);
                if newton_result.width()
                    < interval.width() * BigRational::new(BigInt::from(9), BigInt::from(10))
                {
                    newton_result
                } else {
                    self.refine_bisection(interval)
                }
            }
        }
    }

    /// Refine interval using bisection.
    fn refine_bisection(&mut self, interval: &IsolatingInterval) -> IsolatingInterval {
        self.stats.bisection_steps += 1;

        let mid = interval.midpoint();
        let sign_mid = self.eval_sign(&mid);

        if sign_mid == 0 {
            // Exact root
            return IsolatingInterval::new(mid.clone(), mid, 0, 0);
        }

        if sign_mid != interval.sign_lower {
            // Root in [lower, mid]
            IsolatingInterval::new(interval.lower.clone(), mid, interval.sign_lower, sign_mid)
        } else {
            // Root in [mid, upper]
            IsolatingInterval::new(mid, interval.upper.clone(), sign_mid, interval.sign_upper)
        }
    }

    /// Refine interval using Newton's method.
    fn refine_newton(&mut self, interval: &IsolatingInterval) -> IsolatingInterval {
        let mid = interval.midpoint();
        let f_mid = self.poly.eval(&mid);
        let df_mid = self.poly.derivative().eval(&mid);

        if df_mid.is_zero() {
            // Derivative is zero - fall back to bisection
            return self.refine_bisection(interval);
        }

        // Newton step: x_new = x - f(x)/f'(x)
        let x_new = &mid - (&f_mid / &df_mid);

        // Ensure new point is strictly inside interval
        if x_new > interval.lower && x_new < interval.upper {
            let sign_new = self.eval_sign(&x_new);

            if sign_new == 0 {
                return IsolatingInterval::new(x_new.clone(), x_new, 0, 0);
            }

            if sign_new != interval.sign_lower {
                IsolatingInterval::new(interval.lower.clone(), x_new, interval.sign_lower, sign_new)
            } else {
                IsolatingInterval::new(x_new, interval.upper.clone(), sign_new, interval.sign_upper)
            }
        } else {
            // Newton step escaped the interval - use bisection
            self.refine_bisection(interval)
        }
    }

    /// Get statistics.
    pub fn stats(&self) -> &IsolationStats {
        &self.stats
    }

    /// Reset statistics.
    pub fn reset_stats(&mut self) {
        self.stats = IsolationStats::default();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rat(n: i64) -> BigRational {
        BigRational::from(BigInt::from(n))
    }

    #[test]
    fn test_isolator_creation() {
        let poly = Polynomial::new(vec![rat(-2), rat(0), rat(1)]);

        let isolator = RootIsolator::default_config(poly);
        assert_eq!(isolator.stats().roots_isolated, 0);
    }

    #[test]
    fn test_root_bounds() {
        let poly = Polynomial::new(vec![rat(-6), rat(5), rat(1)]); // x^2 + 5x - 6

        let isolator = RootIsolator::default_config(poly);
        let (lower, upper) = isolator.root_bounds();

        // Roots are -6 and 1, so bounds should contain both
        assert!(lower < rat(-6));
        assert!(upper > rat(1));
    }

    #[test]
    fn test_isolate_linear() {
        let poly = Polynomial::new(vec![rat(-5), rat(1)]); // x - 5

        let mut isolator = RootIsolator::default_config(poly);
        let intervals = isolator.isolate_roots();

        assert_eq!(intervals.len(), 1);
        assert!(intervals[0].lower <= rat(5));
        assert!(intervals[0].upper >= rat(5));
    }

    #[test]
    fn test_refine_bisection() {
        let poly = Polynomial::new(vec![rat(-2), rat(0), rat(1)]); // x^2 - 2

        let mut isolator = RootIsolator::default_config(poly);

        let interval = IsolatingInterval::new(rat(1), rat(2), -1, 1);

        let refined = isolator.refine_interval(&interval, IntervalRefinement::Bisection);

        assert!(refined.width() < interval.width());
    }

    #[test]
    fn test_stats() {
        let poly = Polynomial::new(vec![rat(-5), rat(1)]);

        let mut isolator = RootIsolator::default_config(poly);
        isolator.isolate_roots();

        assert!(isolator.stats().roots_isolated > 0);
        assert!(isolator.stats().sign_evaluations > 0);
    }

    // ========  ========
    // `isolate_in_interval` bisection-depth regression tests (audit: no
    // bound at all on the bisection recursion; `oxiz-nlsat`'s sibling
    // implementation of the same algorithm already carries a 4096-level
    // safety net).
    // ========  ========

    #[test]
    fn test_isolate_roots_multiple_roots_via_bisection_behaviour_preserved() {
        // x^2 - 2 has two real roots (±sqrt(2)); the Cauchy bound brackets
        // both in one interval, so isolate_roots must bisect to separate
        // them. This exact path (isolate_in_interval's num_roots > 1
        // branch) had no prior test coverage in this file.
        let poly = Polynomial::new(vec![rat(-2), rat(0), rat(1)]);
        let mut isolator = RootIsolator::default_config(poly);
        let intervals = isolator.isolate_roots();

        assert_eq!(intervals.len(), 2, "x^2 - 2 has exactly two real roots");
        assert!(intervals[0].lower <= intervals[0].upper);
        assert!(intervals[1].lower <= intervals[1].upper);
        // The two isolating intervals must be disjoint (one entirely below
        // the other), in either order.
        assert!(
            intervals[0].upper <= intervals[1].lower || intervals[1].upper <= intervals[0].lower,
            "isolating intervals must not overlap: {:?}",
            intervals
        );
        assert!(
            !isolator.stats().incomplete,
            "a normal, well-separated polynomial must never hit the depth cap"
        );
        assert_eq!(isolator.stats().roots_isolated, 2);
    }

    #[test]
    fn test_isolate_in_interval_bounded_depth_cap_is_visible_not_silent() {
        // x^3 - x = x(x-1)(x+1) has three real roots. With a bisection
        // budget too small to separate all three, the search must stop and
        // record `stats.incomplete = true` -- never hang, never fabricate a
        // merged interval that falsely claims to isolate multiple roots.
        let poly = Polynomial::new(vec![rat(0), rat(-1), rat(0), rat(1)]);
        let mut isolator = RootIsolator::default_config(poly);
        let (lower, upper) = isolator.root_bounds();

        let results = isolator.isolate_in_interval_bounded(lower, upper, 1);

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
    fn test_isolate_in_interval_bounded_sufficient_depth_never_marks_incomplete() {
        // The same cubic with a depth budget known to be sufficient (the
        // default MAX_ROOT_ISOLATION_DEPTH) must isolate all three roots
        // and never set `incomplete`.
        let poly = Polynomial::new(vec![rat(0), rat(-1), rat(0), rat(1)]);
        let mut isolator = RootIsolator::default_config(poly);
        let intervals = isolator.isolate_roots();

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
                // p(x) = x*(x - eps) = x^2 - eps*x
                let poly = Polynomial::new(vec![rat(0), -eps, rat(1)]);
                let mut isolator = RootIsolator::default_config(poly);
                let intervals = isolator.isolate_roots();
                assert_eq!(intervals.len(), 2);
                assert!(!isolator.stats().incomplete);
            })
            .expect("spawning a thread with an explicit stack size must succeed");
        handle
            .join()
            .expect("a deep-but-finite bisection must not overflow a 1 MiB stack");
    }
}
