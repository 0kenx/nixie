// Copyright 2026 COOLJAPAN OU (Team KitaSan)
// SPDX-License-Identifier: Apache-2.0

use super::delta::DeltaRational;
use crate::config::SimplexConfig;
#[allow(unused_imports)]
use crate::prelude::*;
use num_rational::Rational64;
use num_traits::{One, Signed, Zero};
#[cfg(feature = "profiling")]
use oxiz_core::profiling::{ProfilingCategory, ScopedTimer};
use smallvec::SmallVec;
use std::sync::Arc;
/// Variable index
pub type VarId = u32;

/// Tableau rows and basic-variable flags captured at one decision scope.
///
/// Rows are `Arc`-shared so a snapshot is a *shallow* map clone and a pivot
/// only deep-copies the rows it actually edits (copy-on-write via
/// `Arc::make_mut`): snapshotting the full tableau per decision level used
/// to deep-clone thousands of rows, which dominated QF_AUFLIA runtimes.
type TableauSnapshot = (
    FxHashMap<VarId, Arc<LinExpr>>,
    Vec<bool>,
    FxHashMap<VarId, Arc<SmallVec<[VarId; 4]>>>,
);

/// Canonical identity of a linear form: terms sorted by VarId with merged
/// coefficients and zero coefficients dropped, plus the constant.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct LinKey {
    terms: Vec<(VarId, Rational64)>,
    constant: Rational64,
}

/// Throwaway diagnostic counters for the theory-combination probe-cost
/// investigation (gated on `std`; print on `OXIZ_DIAG`).
#[cfg(feature = "std")]
pub mod diag {
    use std::cell::Cell;
    use std::sync::atomic::{AtomicU64, Ordering};
    std::thread_local! { static PROBE: Cell<bool> = const { Cell::new(false) }; }
    pub static CHECKS_TOTAL: AtomicU64 = AtomicU64::new(0);
    pub static CHECKS_PROBE: AtomicU64 = AtomicU64::new(0);
    pub static CRASH_TOTAL: AtomicU64 = AtomicU64::new(0);
    pub static CRASH_PROBE: AtomicU64 = AtomicU64::new(0);
    pub static PIVOTS_TOTAL: AtomicU64 = AtomicU64::new(0);
    pub static PIVOTS_PROBE: AtomicU64 = AtomicU64::new(0);
    pub static CRASH_NS: AtomicU64 = AtomicU64::new(0);
    pub static FEASIBLE_NS: AtomicU64 = AtomicU64::new(0);
    /// Scoped wall-clock timer that adds elapsed nanos to `target` on drop
    /// (so early returns in the timed function are covered).
    pub struct Timer {
        start: std::time::Instant,
        target: &'static AtomicU64,
    }
    impl Timer {
        pub fn new(target: &'static AtomicU64) -> Self {
            Self {
                start: std::time::Instant::now(),
                target,
            }
        }
    }
    impl Drop for Timer {
        fn drop(&mut self) {
            self.target
                .fetch_add(self.start.elapsed().as_nanos() as u64, Ordering::Relaxed);
        }
    }
    #[inline]
    fn probe() -> bool {
        PROBE.with(|p| p.get())
    }
    pub fn reset() {
        for c in [
            &CHECKS_TOTAL,
            &CHECKS_PROBE,
            &CRASH_TOTAL,
            &CRASH_PROBE,
            &PIVOTS_TOTAL,
            &PIVOTS_PROBE,
        ] {
            c.store(0, Ordering::Relaxed);
        }
        CRASH_NS.store(0, Ordering::Relaxed);
        FEASIBLE_NS.store(0, Ordering::Relaxed);
    }
    pub(crate) fn inc_check() {
        CHECKS_TOTAL.fetch_add(1, Ordering::Relaxed);
        if probe() {
            CHECKS_PROBE.fetch_add(1, Ordering::Relaxed);
        }
    }
    pub(crate) fn inc_crash() {
        CRASH_TOTAL.fetch_add(1, Ordering::Relaxed);
        if probe() {
            CRASH_PROBE.fetch_add(1, Ordering::Relaxed);
        }
    }
    pub(crate) fn inc_pivot() {
        PIVOTS_TOTAL.fetch_add(1, Ordering::Relaxed);
        if probe() {
            PIVOTS_PROBE.fetch_add(1, Ordering::Relaxed);
        }
    }
    pub fn print() {
        let (ct, cp, krt, krp, pt, pp, cns, fns) = (
            CHECKS_TOTAL.load(Ordering::Relaxed),
            CHECKS_PROBE.load(Ordering::Relaxed),
            CRASH_TOTAL.load(Ordering::Relaxed),
            CRASH_PROBE.load(Ordering::Relaxed),
            PIVOTS_TOTAL.load(Ordering::Relaxed),
            PIVOTS_PROBE.load(Ordering::Relaxed),
            CRASH_NS.load(Ordering::Relaxed),
            FEASIBLE_NS.load(Ordering::Relaxed),
        );
        let npc = ct.saturating_sub(cp);
        let npp = pt.saturating_sub(pp);
        let per_probe = if cp > 0 {
            pp as f64 / cp as f64
        } else {
            f64::NAN
        };
        let per_solve = if npc > 0 {
            npp as f64 / npc as f64
        } else {
            f64::NAN
        };
        let ratio = if per_solve > 0.0 {
            per_probe / per_solve
        } else {
            f64::NAN
        };
        let crash_per = if krt > 0 {
            cns as f64 / krt as f64
        } else {
            0.0
        };
        let feas_per = if ct > 0 { fns as f64 / ct as f64 } else { 0.0 };
        eprintln!(
            "[diag] checks total={} probe={} | crash_basis total={} probe={} | pivots total={} probe={}",
            ct, cp, krt, krp, pt, pp
        );
        eprintln!(
            "[diag] pivots/check: probe={:.1}  solve={:.1}  ratio={:.2}x",
            per_probe, per_solve, ratio
        );
        eprintln!(
            "[diag] ns/call: crash_basis={:.0}  make_feasible={:.0}",
            crash_per, feas_per
        );
    }
    /// Print timing shares against the total solve wall-clock.
    pub fn print_timing(total_ns: u64) {
        let cns = CRASH_NS.load(Ordering::Relaxed);
        let fns = FEASIBLE_NS.load(Ordering::Relaxed);
        let tf = fns as f64 / total_ns as f64 * 100.0;
        let tc = cns as f64 / total_ns as f64 * 100.0;
        let tms = total_ns as f64 / 1_000_000.0;
        eprintln!(
            "[diag] wall={:.0}ms  crash_basis={:.1}%  make_feasible={:.1}%",
            tms, tc, tf
        );
    }
}
/// GCD of two `i128` values (used by the checked-rational helpers below to
/// reduce results computed via `i128` intermediates before narrowing back
/// to `i64`).
fn gcd_i128(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}
/// Euclidean GCD on `i64` – hardware division, no software 128-bit path.
/// `gcd_i128` above stays for the genuine wide case.
///
/// Uses the binary (Stein) algorithm on `u64`: the Euclidean loop's chained
/// `idiv`s have ~40-cycle latency each and dominate the pivot loop when the
/// tableau is rational-dense; shift/subtract iterations are a few cycles and
/// the whole gcd runs in a fraction of the divisions' latency for the mixed
/// magnitudes pivot coefficients take.
fn gcd_i64(a: i64, b: i64) -> i64 {
    let mut x = a.unsigned_abs();
    let mut y = b.unsigned_abs();
    if x == 0 {
        return y as i64;
    }
    if y == 0 {
        return x as i64;
    }
    let zx = x.trailing_zeros();
    let zy = y.trailing_zeros();
    x >>= zx;
    y >>= zy;
    let k = zx.min(zy);
    // Both operands are odd from here on, so their difference is even and
    // every subtraction is followed by at least one shift.
    loop {
        if x > y {
            std::mem::swap(&mut x, &mut y);
        }
        y -= x;
        if y == 0 {
            return (x << k) as i64;
        }
        y >>= y.trailing_zeros();
    }
}

/// Fused `x + f·y` on `Rational64` – the exact operation the pivot
/// substitution performs per term.  The integer fast path (`f`, `y` and `x`
/// all integral) is two checked `i64` multiplies/adds and *no gcd at all*;
/// the general path reduces `f·y` cross-wise (GMP `mpq` shape) and adds via
/// the least common multiple.  Semantically identical to
/// `checked_add_r64(x, checked_mul_r64(f, y)?)?` – the fusion only removes
/// intermediate reductions.
/// Checked `DeltaRational · Rational64` (both components), used by the
/// pivot's delta-propagation.  `None` on overflow – callers must re-derive
/// rather than store a wrapped (wrong) assignment.
fn checked_mul_delta(d: DeltaRational, c: Rational64) -> Option<DeltaRational> {
    Some(DeltaRational {
        real: checked_mul_r64(d.real, c)?,
        delta: checked_mul_r64(d.delta, c)?,
    })
}

/// Checked `DeltaRational + DeltaRational`; see [`checked_mul_delta`].
fn checked_add_delta(a: DeltaRational, b: DeltaRational) -> Option<DeltaRational> {
    Some(DeltaRational {
        real: checked_add_r64(a.real, b.real)?,
        delta: checked_add_r64(a.delta, b.delta)?,
    })
}

fn checked_mul_add_r64(x: Rational64, f: Rational64, y: Rational64) -> Option<Rational64> {
    if x.denom() == &1 && f.denom() == &1 && y.denom() == &1 {
        let fy = f.numer().checked_mul(*y.numer())?;
        return Rational64::new_raw(x.numer().checked_add(fy)?, 1).into();
    }
    let prod = checked_mul_r64(f, y)?;
    checked_add_r64(x, prod)
}

/// Build a fully-reduced `Rational64` from an `i128` numerator/denominator
/// pair, returning `None` if the reduced value does not fit back into
/// `i64`. All of the checked-rational helpers below route through this so
/// that a value which cannot be represented as a `Rational64` is reported
/// as `None` (overflow) rather than silently truncated.
///
/// Fast path: when both components already fit in `i64` – which is the
/// overwhelming common case, since tableau coefficients only grow past
/// `i64` after long pivot chains – the reduction stays entirely in `i64`,
/// whose Euclidean gcd compiles to hardware `idiv`.  Routing those through
/// the `i128` gcd instead dominated pivot runtime on dense LIA rows
/// (CAV_2009: ~75% of cycles in `__umodti3`/`u128_div_rem`, the software
/// 128-bit division the `i128` gcd lowers to).
fn checked_ratio_i128(numer: i128, denom: i128) -> Option<Rational64> {
    if denom == 0 {
        return None;
    }
    // Canonical sign first (numerator carries the sign, denominator > 0):
    // callers such as `checked_div_r64` build the denominator from another
    // rational's *numerator*, so negative denominators arrive here
    // routinely, and every one of them would take the software-128-bit
    // path even when the magnitude is tiny.
    let (numer, denom) = if denom < 0 {
        (-numer, -denom)
    } else {
        (numer, denom)
    };
    // Fast path when both components already fit `i64` (the common case):
    // the reduction stays in `i64`, whose Euclidean gcd compiles to
    // hardware division.  Routing those through the `i128` gcd instead
    // dominated pivot runtime on dense LIA rows (the software 128-bit
    // division it lowers to was ~75% of cycles on CAV_2009).
    if numer >= i64::MIN as i128 && numer <= i64::MAX as i128 && denom <= i64::MAX as i128 {
        let mut n = numer as i64;
        let mut d = denom as i64;
        let g = gcd_i64(n, d);
        if g > 1 {
            n /= g;
            d /= g;
        }
        return Some(Rational64::new_raw(n, d));
    }
    let g = gcd_i128(numer, denom);
    let g = if g == 0 { 1 } else { g };
    let n = numer / g;
    let d = denom / g;
    if !(i64::MIN as i128..=i64::MAX as i128).contains(&n) || d > i64::MAX as i128 {
        return None;
    }
    // `new_raw` (not `new`): already reduced above, denominator > 0.
    Some(Rational64::new_raw(n as i64, d as i64))
}
/// Checked rational multiplication: `a * b`, via `i128` intermediates.
/// Returns `None` on overflow instead of silently wrapping (the `i64`-based
/// `Rational64` multiplication used by `num-rational`'s `Mul` impl does not
/// check for overflow: it panics in debug builds and silently wraps to a
/// wrong coefficient in release builds).
fn checked_mul_r64(a: Rational64, b: Rational64) -> Option<Rational64> {
    // Cross-wise pre-reduction (the classic exact-rational multiply, as in
    // GMP's `mpq_mul`): cancel gcd(an, bd) and gcd(bn, ad) BEFORE the two
    // multiplies.  The raw cross-products then stay inside `i64` far longer
    // – with denominators around 10⁹ the naive product already exceeds
    // `i64` and every multiply fell into the software-128-bit path (47% of
    // all pivot rationals on CAV_2009), while the reduced products fit.
    // Every division is exact (by the gcd), so the result is identical up
    // to the final `new_raw` canonical form; any overflow falls through to
    // the `i128` general path.
    let (mut an, mut ad) = (*a.numer(), *a.denom());
    let (mut bn, mut bd) = (*b.numer(), *b.denom());
    let g1 = gcd_i64(an, bd);
    if g1 > 1 {
        an /= g1;
        bd /= g1;
    }
    let g2 = gcd_i64(bn, ad);
    if g2 > 1 {
        bn /= g2;
        ad /= g2;
    }
    if let (Some(n), Some(d)) = (an.checked_mul(bn), ad.checked_mul(bd)) {
        return Some(Rational64::new_raw(n, d));
    }
    let numer = (*a.numer() as i128).checked_mul(*b.numer() as i128)?;
    let denom = (*a.denom() as i128).checked_mul(*b.denom() as i128)?;
    checked_ratio_i128(numer, denom)
}
/// Checked rational division: `a / b`. Returns `None` if `b` is zero or the
/// result overflows `i64` after reduction.
fn checked_div_r64(a: Rational64, b: Rational64) -> Option<Rational64> {
    if b.numer() == &0 {
        return None;
    }
    let numer = (*a.numer() as i128).checked_mul(*b.denom() as i128)?;
    let denom = (*a.denom() as i128).checked_mul(*b.numer() as i128)?;
    checked_ratio_i128(numer, denom)
}
/// Checked rational addition: `a + b`. Returns `None` on overflow.
fn checked_add_r64(a: Rational64, b: Rational64) -> Option<Rational64> {
    // Integer fast path: plain checked `i64` add.
    if a.denom() == &1 && b.denom() == &1 {
        return Rational64::new_raw(a.numer().checked_add(*b.numer())?, 1).into();
    }
    // Same-denominator fast path: add numerators, keep the denominator.
    if a.denom() == b.denom() {
        let numer = a.numer().checked_add(*b.numer())?;
        let denom = *a.denom();
        return if denom == 1 {
            Rational64::new_raw(numer, 1).into()
        } else {
            checked_ratio_i128(numer as i128, denom as i128)
        };
    }
    // Least-common-multiple denominators (GMP `mpq_add` shape): scale each
    // numerator by `lcm/dᵢ` instead of cross-multiplying by the *other*
    // denominator, so the common case (one denominator divides the other)
    // needs no product at all and the general case needs products around
    // `lcm`, not `d₁·d₂`.
    let (d1, d2) = (*a.denom(), *b.denom());
    let g = gcd_i64(d1, d2);
    let l2 = d2 / g;
    let l1 = d1 / g;
    if let (Some(s1), Some(s2), Some(denom)) = (
        a.numer().checked_mul(l2),
        b.numer().checked_mul(l1),
        d1.checked_mul(l2),
    ) && let Some(numer) = s1.checked_add(s2)
    {
        let gr = gcd_i64(numer, denom);
        if gr > 1 {
            return Some(Rational64::new_raw(numer / gr, denom / gr));
        }
        return Some(Rational64::new_raw(numer, denom));
    }
    let ad = (*a.numer() as i128).checked_mul(*b.denom() as i128)?;
    let cb = (*b.numer() as i128).checked_mul(*a.denom() as i128)?;
    let numer = ad.checked_add(cb)?;
    let denom = (*a.denom() as i128).checked_mul(*b.denom() as i128)?;
    checked_ratio_i128(numer, denom)
}
/// Checked rational negation: `-a`. Only fails for the `i64::MIN` edge
/// case, whose absolute value has no positive `i64` representation.
fn checked_neg_r64(a: Rational64) -> Option<Rational64> {
    let n = (*a.numer() as i128).checked_neg()?;
    if !(i64::MIN as i128..=i64::MAX as i128).contains(&n) {
        return None;
    }
    // `new_raw`: negating the numerator preserves the reduced form and the
    // denominator is already positive.
    Some(Rational64::new_raw(n as i64, *a.denom()))
}
/// Checked rational reciprocal: `1 / a`. Returns `None` if `a` is zero.
fn checked_recip_r64(a: Rational64) -> Option<Rational64> {
    if a.numer() == &0 {
        return None;
    }
    checked_ratio_i128(*a.denom() as i128, *a.numer() as i128)
}
/// Split a full reason list into `(primary, auxiliary)`, deduplicating so a
/// reason never appears twice. Returns `None` for an empty list (a derived
/// bound with no recorded antecedent is not applied rather than fabricating a
/// reason).
fn split_reasons(reasons: SmallVec<[u32; 4]>) -> Option<(u32, SmallVec<[u32; 4]>)> {
    let mut iter = reasons.into_iter();
    let primary = iter.next()?;
    let mut aux: SmallVec<[u32; 4]> = SmallVec::new();
    for r in iter {
        if r != primary && !aux.contains(&r) {
            aux.push(r);
        }
    }
    Some((primary, aux))
}
/// A linear expression: sum of (coefficient, variable) pairs + constant
#[derive(Debug, Clone, Default)]
pub struct LinExpr {
    /// Terms: (variable, coefficient)
    pub terms: SmallVec<[(VarId, Rational64); 4]>,
    /// Constant term
    pub constant: Rational64,
}
impl LinExpr {
    /// Create a new linear expression
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
    /// Create a constant expression
    #[must_use]
    pub fn constant(c: Rational64) -> Self {
        Self {
            terms: SmallVec::new(),
            constant: c,
        }
    }
    /// Create a variable expression
    #[must_use]
    pub fn var(v: VarId) -> Self {
        Self {
            terms: smallvec::smallvec![(v, Rational64::one())],
            constant: Rational64::zero(),
        }
    }
    /// Add a term
    pub fn add_term(&mut self, var: VarId, coef: Rational64) {
        if !coef.is_zero() {
            for (v, c) in &mut self.terms {
                if *v == var {
                    *c += coef;
                    if c.is_zero() {
                        self.terms.retain(|(v, _)| *v != var);
                    }
                    return;
                }
            }
            self.terms.push((var, coef));
        }
    }
    /// Add a constant
    pub fn add_constant(&mut self, c: Rational64) {
        self.constant += c;
    }
    /// Overflow-checked variant of [`Self::add_term`]: merges `coef` into
    /// the existing coefficient of `var` (or inserts a new term) exactly
    /// like `add_term`, but via `i64`-checked rational addition. Returns
    /// `false` (leaving `self` unmodified) if the merged coefficient would
    /// not fit back into a `Rational64`, instead of silently wrapping.
    #[must_use]
    /// Fused `+= f·coef` for one term: avoids materialising `f·coef` as a
    /// reduced intermediate before adding it to the (possibly absent) existing
    /// entry.  On integral tableaus (fresh LIA rows) this is plain `i64`
    /// multiply-add with zero gcds.
    fn try_add_term_mul(&mut self, var: VarId, f: Rational64, coef: Rational64) -> bool {
        if coef.is_zero() {
            return true;
        }
        for (v, c) in &mut self.terms {
            if *v == var {
                let Some(sum) = checked_mul_add_r64(*c, f, coef) else {
                    return false;
                };
                *c = sum;
                if c.is_zero() {
                    self.terms.retain(|(v, _)| *v != var);
                }
                return true;
            }
        }
        // Term absent: just f·coef.
        let Some(prod) = checked_mul_r64(f, coef) else {
            return false;
        };
        self.terms.push((var, prod));
        true
    }

    fn try_add_term(&mut self, var: VarId, coef: Rational64) -> bool {
        if coef.is_zero() {
            return true;
        }
        for (v, c) in &mut self.terms {
            if *v == var {
                let Some(sum) = checked_add_r64(*c, coef) else {
                    return false;
                };
                *c = sum;
                if c.is_zero() {
                    self.terms.retain(|(v, _)| *v != var);
                }
                return true;
            }
        }
        self.terms.push((var, coef));
        true
    }
    /// Negate the expression
    pub fn negate(&mut self) {
        for (_, c) in &mut self.terms {
            *c = -*c;
        }
        self.constant = -self.constant;
    }
    /// Multiply by a constant
    pub fn scale(&mut self, factor: Rational64) {
        for (_, c) in &mut self.terms {
            *c *= factor;
        }
        self.constant *= factor;
    }
    /// Check if this expression subsumes another (i.e., this is weaker or equal)
    ///
    /// For example, x + y <= 10 subsumes x + y <= 5 (the latter is stronger)
    /// Returns true if adding the other constraint is redundant given this one
    #[must_use]
    pub fn subsumes(&self, other: &LinExpr, self_is_le: bool, other_is_le: bool) -> bool {
        if self.terms.len() != other.terms.len() {
            return false;
        }
        for (i, (v1, c1)) in self.terms.iter().enumerate() {
            if let Some((v2, c2)) = other.terms.get(i) {
                if v1 != v2 || c1 != c2 {
                    return false;
                }
            } else {
                return false;
            }
        }
        match (self_is_le, other_is_le) {
            (true, true) => self.constant >= other.constant,
            (false, false) => self.constant <= other.constant,
            _ => false,
        }
    }
}
/// Bound type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub enum BoundType {
    /// No bound
    None,
    /// Lower bound (x >= b)
    Lower,
    /// Upper bound (x <= b)
    Upper,
    /// Equality (x = b)
    Equal,
}
/// A bound on a variable
#[derive(Debug, Clone)]
pub struct Bound {
    /// Bound type
    pub kind: BoundType,
    /// Bound value (supports strict bounds via delta)
    pub value: DeltaRational,
    /// Primary reason (assertion that caused this bound).
    pub reason: u32,
    /// Additional contributing reasons beyond `reason`. Populated when this
    /// bound was *derived* by propagation from several non-basic-variable
    /// bounds (see [`Simplex::propagate_bounds`] / [`Simplex::tighten_bounds`]):
    /// such a derived bound is implied by ALL of the bounds that fed the
    /// derivation, not just one. Conflict explanations
    /// ([`Simplex::explain_conflict`] and the bound-crossing check in
    /// [`Simplex::check`]) must emit `reason` together with every entry here,
    /// otherwise the Farkas/conflict clause is incomplete -- an unsound
    /// explanation that omits genuine antecedents.
    pub aux_reasons: SmallVec<[u32; 4]>,
}
impl Bound {
    /// Iterate over every reason (primary + auxiliary) backing this bound.
    pub(super) fn all_reasons(&self) -> impl Iterator<Item = u32> + '_ {
        core::iter::once(self.reason).chain(self.aux_reasons.iter().copied())
    }
}
/// A propagated bound derived from constraint analysis
#[derive(Debug, Clone)]
pub struct PropagatedBound {
    /// The variable that got a new bound
    pub var: VarId,
    /// Whether it's a lower bound (true) or upper bound (false)
    pub is_lower: bool,
    /// The bound value
    pub value: DeltaRational,
    /// The reasons (assertion IDs) that imply this bound
    pub reasons: SmallVec<[u32; 4]>,
}
/// An undo entry for reverting a bound change
#[derive(Debug, Clone)]
enum BoundUndo {
    /// Lower bound was None, now has a value
    LowerWasNone(VarId),
    /// Lower bound was Some, save old value
    LowerWasSome(VarId, Bound),
    /// Upper bound was None, now has a value
    UpperWasNone(VarId),
    /// Upper bound was Some, save old value
    UpperWasSome(VarId, Bound),
}
/// Simplex tableau state
#[derive(Debug)]
pub struct Simplex {
    /// A bound-crossing conflict (lower > upper on one variable) recorded by
    /// the most recent bound assertion that completed the crossing pair, not
    /// yet consumed by a probe (see [`Self::bound_crossing_conflict`]).
    /// `None` when no crossing is pending.
    ///
    /// This is what makes the probe O(1): the crossing can only appear at
    /// the moment the SECOND bound of the pair is set (assignments shift,
    /// bounds do not), so recording it there – with both bounds' full reason
    /// antecedents – turns the literal-time probe from an O(variables) scan
    /// into a take.  Cleared on `pop`: a backtrack removes the asserting
    /// literal, and reporting a conflict whose bounds no longer hold would
    /// blame literals that are no longer assigned.
    pending_crossing: Option<Vec<u32>>,
    /// Number of original variables
    num_vars: usize,
    /// Number of slack variables
    num_slack: usize,
    /// Current assignment (using delta-rationals for strict bounds)
    assignment: Vec<DeltaRational>,
    /// Lower bounds
    lower: Vec<Option<Bound>>,
    /// Upper bounds
    upper: Vec<Option<Bound>>,
    /// Tableau rows: basic variable -> linear combination of non-basic
    tableau: FxHashMap<VarId, Arc<LinExpr>>,
    /// Column index: non-basic variable -> basic variables whose rows
    /// reference it.  Lets a bound change on one variable update exactly the
    /// rows that depend on it (O(column)) instead of re-deriving the whole
    /// tableau (`update_assignment`, O(tableau·terms)) after every pop or
    /// bound assertion – the Dutertre–de Moura incremental-assignment
    /// maintenance structure.  Kept in lockstep with `tableau` by
    /// `intern_row` and `pivot`.
    columns: FxHashMap<VarId, Arc<SmallVec<[VarId; 4]>>>,
    /// Content-addressed row identities: canonical linear form (over stable
    /// VarIds) -> the slack whose row defines it.  Every `add_*` constraint
    /// API routes through [`Self::intern_row_cached`], so repeated assertions
    /// of the same form – from either polarity of an atom, SAT re-sends, or
    /// scratch scopes like the entailed-equality probes – share ONE row and
    /// differ only in the (scoped, trailed) bounds they set on it.  Without
    /// this, every call allocated a permanent row, and the probe paths alone
    /// grew the tableau without bound.
    ///
    /// Entries are validated against the tableau on every lookup
    /// ([`Self::intern_row_cached`]): rows interned inside a decision scope
    /// are REMOVED by that scope's `pop` (see `row_scope_trail`), and a cache
    /// entry naming a removed row simply misses and re-interns.
    row_ids: FxHashMap<LinKey, VarId>,
    /// Rows (slack ids) interned inside the current decision scope, in
    /// insertion order; `pop` removes them (and, transitively, any surviving
    /// row that references them) from the tableau, mirroring the old
    /// `NewSlack` structural undo.  Unlike that undo, VarIds themselves are
    /// never recycled – only the ROWS die – so term interning, the parallel
    /// arrays and every cached VarId stay valid forever.
    row_scope_trail: Vec<VarId>,
    /// Marks into `row_scope_trail`, parallel to `trail_limits`.
    row_scope_marks: Vec<usize>,
    /// Basic variables
    basic: Vec<bool>,
    /// Infeasible basic variable (if any)
    infeasible: Option<VarId>,
    /// Pending propagated bounds
    propagated: Vec<PropagatedBound>,
    /// Trail of undo operations
    trail: Vec<BoundUndo>,
    /// Trail size at each decision level
    trail_limits: Vec<usize>,
    /// Cached assignments for warm-starting (basis caching)
    /// Saves assignment state at each decision level for faster incremental solving
    cached_assignments: Vec<Option<Vec<DeltaRational>>>,
    /// Lazily saved tableau snapshots for correct restoration on pop.
    /// Pivoting during `check()` modifies rows in-place, so the first operation
    /// that can mutate a scoped basis snapshots it.  A decision level that only
    /// accumulates trailed bounds/rows needs no full-tableau clone.
    saved_tableaux: Vec<Option<TableauSnapshot>>,
    /// Pivoting rule to use
    /// Maximum number of pivot operations before giving up
    max_pivots: usize,
    /// Set to `true` when the most recent `check()`/`dual_simplex()` aborted
    /// because it hit `max_pivots` without proving feasibility or infeasibility.
    ///
    /// When this flag is set, an `Ok(())` result from `check()` MUST NOT be
    /// interpreted as "satisfiable" – the LP state is unresolved (an incomplete
    /// resource-limited run), and callers deciding satisfiability have to report
    /// `Unknown` rather than `Sat`.  See [`Simplex::resource_limit_reached`].
    resource_limit: bool,
    /// Whether `assignment[]` is consistent with the current tableau+bounds
    /// (incrementally maintained on `add_le`/basic-bound changes).  When true,
    /// `check()` may skip the O(tableau) `crash_basis` re-derivation and go
    /// straight to `make_feasible`.  Conservatively cleared on non-basic bound
    /// changes and on `pop` (where restoring is cheaper than proving
    /// consistency).  Dutertre–de-Ma-style incremental assignment, adapted to
    /// oxiz's slack-per-constraint tableau.
    assignment_current: bool,
}
impl Default for Simplex {
    fn default() -> Self {
        Self::new()
    }
}
impl Simplex {
    /// Create a new Simplex instance
    #[must_use]
    pub fn new() -> Self {
        Self::with_config(SimplexConfig::default())
    }
    /// Create a new Simplex instance with custom configuration
    #[must_use]
    pub fn with_config(config: SimplexConfig) -> Self {
        Self {
            num_vars: 0,
            num_slack: 0,
            pending_crossing: None,
            assignment: Vec::new(),
            lower: Vec::new(),
            upper: Vec::new(),
            tableau: FxHashMap::default(),
            columns: FxHashMap::default(),
            row_ids: FxHashMap::default(),
            row_scope_trail: Vec::new(),
            row_scope_marks: vec![0],
            basic: Vec::new(),
            infeasible: None,
            propagated: Vec::new(),
            trail: Vec::new(),
            trail_limits: vec![0],
            cached_assignments: Vec::new(),
            saved_tableaux: Vec::new(),
            max_pivots: config.max_pivots,
            resource_limit: false,
            assignment_current: true,
        }
    }
    /// Record that `row`'s tableau row now references `var`.
    ///
    /// Column lists are `Arc`-shared with scope snapshots (copy-on-write):
    /// an edit clones exactly the one list it touches, so the snapshot a
    /// Unchecked variants for call sites that PROVE membership (or its
    /// absence) from the column-exactness invariant: skip the linear scan.
    fn column_drop_known(&mut self, var: VarId, row: VarId) {
        if let Some(col_arc) = self.columns.get_mut(&var) {
            let col = Arc::make_mut(col_arc);
            if let Some(pos) = col.iter().position(|&r| r == row) {
                col.swap_remove(pos);
            }
        }
    }

    fn column_push_known(&mut self, var: VarId, row: VarId) {
        match self.columns.get_mut(&var) {
            Some(col_arc) => Arc::make_mut(col_arc).push(row),
            None => {
                self.columns
                    .insert(var, Arc::new(SmallVec::from_slice(&[row])));
            }
        }
    }

    /// Snap the non-basic variable at `idx` into its (possibly just changed)
    /// bound window and propagate the resulting value delta through every
    /// row that references it, keeping basic assignments consistent with the
    /// tableau.  O(column of `idx`).
    ///
    /// This is the Dutertre–de Moura incremental assignment update for a
    /// non-basic bound change; it replaces the previous "mark the whole
    /// assignment stale and re-derive the tableau on the next `check`"
    /// behaviour, which cost O(tableau·terms) on every pop/assert.
    fn on_nonbasic_bound_change(&mut self, idx: usize) {
        if idx >= self.assignment.len() || self.is_basic(idx) {
            return;
        }
        let var = idx as VarId;
        let old = self.assignment[idx];
        let mut new = old;
        if let Some(lo) = &self.lower[idx]
            && new < lo.value
        {
            new = lo.value;
        }
        if let Some(hi) = &self.upper[idx]
            && new > hi.value
        {
            new = hi.value;
        }
        if new == old {
            return;
        }
        self.assignment[idx] = new;
        let delta = new - old;
        // Deep-copy the column list: updating assignments mutates nothing in
        // `columns`, but the borrow checker needs the split.
        let dependents: SmallVec<[VarId; 4]> = self
            .columns
            .get(&var)
            .map(|c| (**c).clone())
            .unwrap_or_default();
        for b in dependents {
            let bi = b as usize;
            if bi >= self.assignment.len() {
                continue;
            }
            let coef = self
                .tableau
                .get(&b)
                .and_then(|row| row.terms.iter().find(|(v, _)| *v == var).map(|(_, c)| *c));
            if let Some(c) = coef {
                self.assignment[bi] += delta * c;
            }
        }
    }

    /// TEMP debug: dump the tableau rows.
    /// TEMP DIAG helper reused by tests.
    pub fn dbg_tableau(&self) -> String {
        use std::fmt::Write;
        let mut out = String::new();
        let _ = writeln!(out, "rows={}", self.tableau.len());
        let mut rows: Vec<_> = self.tableau.iter().collect();
        rows.sort_by_key(|(v, _)| **v);
        for (v, row) in rows {
            let _ = writeln!(
                out,
                "  s{} = {:?} + {:?}  [val={:?} lo={:?} hi={:?} basic={}]",
                v,
                row.constant,
                row.terms
                    .iter()
                    .map(|(t, c)| (t.to_string(), c.to_string()))
                    .collect::<Vec<_>>(),
                self.assignment.get(*v as usize),
                self.lower
                    .get(*v as usize)
                    .and_then(|b| b.as_ref().map(|b| b.value)),
                self.upper
                    .get(*v as usize)
                    .and_then(|b| b.as_ref().map(|b| b.value)),
                self.basic.get(*v as usize).copied().unwrap_or(false),
            );
        }
        out
    }

    /// Whether the most recent feasibility run (`check` / `dual_simplex`) gave up
    /// after exhausting the pivot budget without a definitive answer.
    ///
    /// If this returns `true`, the last `Ok(())` is a *resource limit*, not a
    /// proof of feasibility, and any satisfiability decision built on top of the
    /// simplex must be reported as `Unknown`.
    #[inline]
    #[must_use]
    pub fn resource_limit_reached(&self) -> bool {
        self.resource_limit
    }
    /// Grow every per-variable parallel array by exactly one slot, in
    /// lockstep, and return the new (non-basic) variable's id.
    ///
    /// This is the *single* choke point through which `assignment`, `lower`,
    /// `upper` and `basic` gain a slot for an ordinary variable, so the four
    /// arrays can never drift out of length relative to one another. A
    /// matching `NewVar` undo record is pushed so that [`Self::pop`] shrinks
    /// all four together.
    fn register_var(&mut self) -> VarId {
        let id = self.assignment.len() as VarId;
        self.num_vars += 1;
        self.assignment.push(DeltaRational::zero());
        self.lower.push(None);
        self.upper.push(None);
        self.basic.push(false);
        // Variables are search-global (Z3 `lar_solver` / Dutertre–de Moura):
        // a VarId, once allocated, is never recycled, so a tableau row may
        // reference it at any decision level.  Only BOUNDS are scoped and
        // trailed.  (Recycling VarIds on pop forced rows to be scoped too,
        // which re-created every atom's row at each level that re-asserted
        // it – thousands of duplicate rows on QF_AUFLIA.)
        id
    }
    /// Ensure every per-variable array covers index `idx`, materializing any
    /// missing slots (contiguously, including gaps) as fresh unconstrained,
    /// non-basic variables via [`Self::register_var`].
    ///
    /// Every code path that can hand a variable index to the tableau or the
    /// bounds arrays routes through this, so a variable index the caller
    /// cached and replayed across a backtrack (which shrank the arrays) – or
    /// any other stale/out-of-range index – can never index past the parallel
    /// arrays and panic. The replayed index is simply reinstated as a fresh
    /// variable, and the `NewVar` undo records pushed here keep `pop` correct.
    fn ensure_var(&mut self, idx: usize) {
        while self.assignment.len() <= idx {
            let _ = self.register_var();
        }
    }
    /// Add a new variable
    pub fn new_var(&mut self) -> VarId {
        self.register_var()
    }
    /// Add a slack variable for a constraint
    fn new_slack(&mut self) -> VarId {
        let id = self.assignment.len() as VarId;
        self.num_slack += 1;
        self.assignment.push(DeltaRational::zero());
        self.lower.push(None);
        self.upper.push(None);
        self.basic.push(true);
        // See `register_var`: slack rows are search-global definitions
        // (`slack = <linear form>`); they constrain nothing until a bound
        // is set on them, so keeping them across backtracks is sound and
        // makes one row serve every level that asserts its atom.
        id
    }
    /// Get the current value of a variable (returns the real part)
    #[inline]
    #[must_use]
    pub fn value(&self, var: VarId) -> Rational64 {
        self.assignment
            .get(var as usize)
            .map(|d| d.real)
            .unwrap_or_default()
    }
    /// Get the current delta-rational value of a variable
    #[inline]
    #[must_use]
    pub fn delta_value(&self, var: VarId) -> DeltaRational {
        self.assignment
            .get(var as usize)
            .copied()
            .unwrap_or_default()
    }
    /// Concrete positive rational to substitute for the infinitesimal `δ` when
    /// turning the delta-rational assignment into an ordinary rational model.
    ///
    /// A strict bound such as `x > 0` is stored as the delta-rational lower
    /// bound `(0, 1)` and the assignment then sits at `0 + δ`.  Reading back
    /// only the real part reports `x = 0`, which *violates* the very constraint
    /// that produced it.  The fix is the standard δ-instantiation of
    /// Dutertre & de Moura's "Simplex for DPLL(T)": pick the largest `δ₀ ∈ (0,1]`
    /// for which every bound still holds after substituting `δ := δ₀`.
    ///
    /// Each bound contributes a constraint of the form `dr + dd·δ ≥ 0` where
    /// `dr`/`dd` are the real/delta gaps between the assignment and the bound.
    /// Only `dd < 0` can be violated by a large δ, and feasibility of the
    /// delta-rational assignment guarantees `dr > 0` in that case, so the
    /// binding limit is `δ ≤ dr / (-dd)`.  Tableau rows are linear in δ and are
    /// preserved by any substitution, so bounds are the only source of
    /// constraints.
    ///
    /// Reference: Z3's `lp::lar_solver::get_model` delta adjustment.
    #[must_use]
    pub fn delta_instantiation(&self) -> Rational64 {
        // Smallest representable positive rational, used as a conservative
        // fallback when an exact ratio overflows `Rational64`.
        let tiny = Rational64::new(1, i64::MAX);
        let mut delta = Rational64::one();
        let mut tighten = |dr: Rational64, dd: Rational64| {
            // Constraint `dr + dd·δ >= 0`.  Non-negative `dd` can never be
            // violated by a positive δ, and a non-positive `dr` means the
            // delta-rational assignment already violates this bound (the state
            // is infeasible) – nothing to instantiate.
            if !dd.is_negative() || !dr.is_positive() {
                return;
            }
            let limit = checked_neg_r64(dd).and_then(|neg_dd| checked_div_r64(dr, neg_dd));
            match limit {
                Some(cand) => {
                    if cand < delta {
                        delta = cand;
                    }
                }
                // Ratio not representable: clamp to the smallest positive value
                // rather than risk keeping a δ that breaks the bound.
                None => {
                    if tiny < delta {
                        delta = tiny;
                    }
                }
            }
        };
        for (idx, assigned) in self.assignment.iter().enumerate() {
            if let Some(bound) = self.lower.get(idx).and_then(Option::as_ref) {
                // assignment >= lower  =>  (a.real - l.real) + (a.delta - l.delta)·δ >= 0
                if let (Some(dr), Some(dd)) = (
                    checked_neg_r64(bound.value.real)
                        .and_then(|n| checked_add_r64(assigned.real, n)),
                    checked_neg_r64(bound.value.delta)
                        .and_then(|n| checked_add_r64(assigned.delta, n)),
                ) {
                    tighten(dr, dd);
                }
            }
            if let Some(bound) = self.upper.get(idx).and_then(Option::as_ref) {
                // assignment <= upper  =>  (u.real - a.real) + (u.delta - a.delta)·δ >= 0
                if let (Some(dr), Some(dd)) = (
                    checked_neg_r64(assigned.real)
                        .and_then(|n| checked_add_r64(bound.value.real, n)),
                    checked_neg_r64(assigned.delta)
                        .and_then(|n| checked_add_r64(bound.value.delta, n)),
                ) {
                    tighten(dr, dd);
                }
            }
        }
        delta
    }
    /// Set a lower bound (x >= value).
    ///
    /// Monotone: a lower bound only ever *tightens*.  With interned rows,
    /// both polarities of an atom and every re-assertion set bounds on the
    /// SAME slack, so a weaker re-assertion (e.g. replaying `x >= 0` from a
    /// resync) must never relax the strict `x >= 0 + δ` a `x > 0` atom set
    /// earlier at a still-live scope – bounds are consequences of asserted
    /// literals, and keeping the tighter of the two can only exclude points
    /// some live atom forbids.  A no-op tightening records nothing, so the
    /// scope pop of the tighter bound still restores correctly (LIFO).
    pub fn set_lower(&mut self, var: VarId, value: Rational64, reason: u32) {
        self.set_lower_delta(
            var,
            DeltaRational::from_rational(value),
            smallvec::smallvec![reason],
        );
    }
    /// Set a lower bound directly from a `DeltaRational` (supports strict
    /// bounds carrying an infinitesimal `δ` component), pushing an undo
    /// record onto `self.trail` exactly like [`Self::set_lower`]. Used by
    /// [`Self::propagate_bounds`], whose derived bound values are already
    /// `DeltaRational` (propagation chains through strict inequalities).
    ///
    /// Takes the FULL set of contributing reasons: the first becomes the
    /// bound's primary `reason`, the remainder its `aux_reasons`, so that a
    /// propagated bound records every antecedent for later conflict
    /// explanation (see [`Bound::aux_reasons`]).
    fn set_lower_delta(&mut self, var: VarId, value: DeltaRational, reasons: SmallVec<[u32; 4]>) {
        let idx = var as usize;
        let Some((reason, aux_reasons)) = split_reasons(reasons) else {
            return;
        };
        self.ensure_var(idx);
        match &self.lower[idx] {
            None => self.trail.push(BoundUndo::LowerWasNone(var)),
            Some(old) => {
                let old = old.clone();
                self.trail.push(BoundUndo::LowerWasSome(var, old));
            }
        }
        self.lower[idx] = Some(Bound {
            kind: BoundType::Lower,
            value,
            reason,
            aux_reasons,
        });
        self.note_bound_change(idx);
        self.record_crossing(idx);
    }
    /// Set an upper bound directly from a `DeltaRational`; see
    /// [`Self::set_lower_delta`].
    fn set_upper_delta(&mut self, var: VarId, value: DeltaRational, reasons: SmallVec<[u32; 4]>) {
        let idx = var as usize;
        let Some((reason, aux_reasons)) = split_reasons(reasons) else {
            return;
        };
        self.ensure_var(idx);
        match &self.upper[idx] {
            None => self.trail.push(BoundUndo::UpperWasNone(var)),
            Some(old) => {
                let old = old.clone();
                self.trail.push(BoundUndo::UpperWasSome(var, old));
            }
        }
        self.upper[idx] = Some(Bound {
            kind: BoundType::Upper,
            value,
            reason,
            aux_reasons,
        });
        self.note_bound_change(idx);
        self.record_crossing(idx);
    }
    /// Set a strict lower bound (x > value), represented as x >= value + δ.
    pub fn set_strict_lower(&mut self, var: VarId, value: Rational64, reason: u32) {
        self.set_lower_delta(
            var,
            DeltaRational::new(value, Rational64::one()),
            smallvec::smallvec![reason],
        );
    }
    /// Set an upper bound (x <= value).  Monotone: see [`Self::set_lower`].
    pub fn set_upper(&mut self, var: VarId, value: Rational64, reason: u32) {
        self.set_upper_delta(
            var,
            DeltaRational::from_rational(value),
            smallvec::smallvec![reason],
        );
    }
    /// Set a strict upper bound (x < value), represented as x <= value - δ.
    pub fn set_strict_upper(&mut self, var: VarId, value: Rational64, reason: u32) {
        self.set_upper_delta(
            var,
            DeltaRational::new(value, -Rational64::one()),
            smallvec::smallvec![reason],
        );
    }
    /// Add a constraint: expr <= 0
    pub fn add_le(&mut self, expr: LinExpr, reason: u32) {
        // Content-addressed slack (`slack = expr`); the constraint is the
        // bound `slack <= 0`.
        let slack = self.intern_row_cached(&expr);
        self.set_upper(slack, Rational64::zero(), reason);
    }

    /// Add a constraint `expr <= 0` justified by a *set* of reasons (the
    /// antecedent atoms whose conjunction implies it – e.g. a Gomory cut
    /// derived from several asserted bounds).  Any conflict the constraint
    /// participates in explains back to the full set, never to just one.
    pub fn add_le_with_reasons(
        &mut self,
        expr: LinExpr,
        reasons: SmallVec<[u32; 4]>,
    ) -> Option<VarId> {
        if reasons.is_empty() {
            return None;
        }
        let slack = self.intern_row_cached(&expr);
        self.set_upper_delta(slack, DeltaRational::zero(), reasons);
        Some(slack)
    }

    /// [`Self::intern_row`] with content addressing: two calls with the same
    /// canonical linear form return the SAME slack.  See `row_ids`.
    pub(crate) fn intern_row_cached(&mut self, expr: &LinExpr) -> VarId {
        let mut key_terms: Vec<(VarId, Rational64)> = Vec::with_capacity(expr.terms.len());
        for &(var, coef) in &expr.terms {
            if coef.is_zero() {
                continue;
            }
            match key_terms.binary_search_by_key(&var, |(v, _)| *v) {
                Ok(i) => key_terms[i].1 += coef,
                Err(i) => key_terms.insert(i, (var, coef)),
            }
        }
        key_terms.retain(|(_, c)| !c.is_zero());
        let key = LinKey {
            terms: key_terms,
            constant: expr.constant,
        };
        if let Some(&slack) = self.row_ids.get(&key)
            && self.tableau.contains_key(&slack)
        {
            return slack;
        }
        let slack = self.intern_row(LinExpr {
            terms: key.terms.iter().copied().collect(),
            constant: key.constant,
        });
        self.row_ids.insert(key, slack);
        slack
    }

    /// Intern a slack variable whose tableau row defines it as exactly
    /// `expr` (i.e. a row `slack - expr = 0` in reduced form), with no
    /// constraint attached, and return its id.
    ///
    /// This is the Dutertre–de Moura / Z3 `lar_solver` constraint
    /// representation: one stable row per distinct linear form, and every
    /// assertion of an atom over that form – at any polarity, at any
    /// decision level, however often the SAT core re-sends it – is just a
    /// *bound update* on the shared slack (O(1), trailed, popped with the
    /// scope that set it).  The pre-existing alternative (a fresh
    /// slack+row per assertion event) made the tableau grow with the number
    /// of literal assignments rather than with the number of distinct
    /// constraints: QF_AUFLIA/swap pushed it past 100k rows for a problem
    /// with ~90 atoms.
    ///
    /// Basic variables are substituted out so the new row references only
    /// non-basic variables, and the slack's assignment is computed
    /// incrementally from its row (Dutertre–de-Ma) instead of forcing the
    /// next `check()` into a full `crash_basis` re-derivation.
    pub fn intern_row(&mut self, expr: LinExpr) -> VarId {
        let mut substituted_expr = LinExpr::constant(expr.constant);
        for (var, coef) in &expr.terms {
            if let Some(basic_expr) = self.tableau.get(var).cloned() {
                substituted_expr.add_constant(coef * basic_expr.constant);
                for (inner_var, inner_coef) in &basic_expr.terms {
                    substituted_expr.add_term(*inner_var, coef * inner_coef);
                }
            } else {
                substituted_expr.add_term(*var, *coef);
            }
        }
        // Register every variable the (substituted) expression references
        // BEFORE allocating the slack, so (a) no tableau row can reference an
        // index past the bounds arrays and (b) the slack's id is guaranteed
        // fresh rather than colliding with an as-yet-unregistered variable.
        if let Some(max_var) = substituted_expr.terms.iter().map(|(v, _)| *v).max() {
            self.ensure_var(max_var as usize);
        }
        let slack = self.new_slack();
        // Row: `slack = expr`.  The tableau row for the basic variable
        // `slack` holds the *right-hand side* it equals, so it must not
        // reference `slack` itself; the substituted expression already
        // excludes every other basic variable, which keeps the row reduced.
        let mut slack_expr = LinExpr::constant(substituted_expr.constant);
        for (var, coef) in &substituted_expr.terms {
            slack_expr.add_term(*var, *coef);
        }
        self.tableau.insert(slack, Arc::new(slack_expr));
        if slack as usize >= self.basic.len() {
            self.basic.resize(slack as usize + 1, false);
        }
        self.basic[slack as usize] = true;
        // Column index bookkeeping for the new row.
        let terms: SmallVec<[(VarId, Rational64); 4]> = {
            let row = self.tableau.get(&slack).expect("slack row just inserted");
            row.terms.iter().copied().collect()
        };
        for (v, _) in terms {
            self.column_push_known(v, slack);
        }
        // Dutertre–de-Ma incremental assignment: the new basic slack's row
        // references only non-basic variables (basic vars were substituted
        // out above), whose assignments are current, so compute the slack's
        // assignment from its row in O(row) instead of forcing `check()` to
        // re-derive the whole tableau via `crash_basis`.
        if self.assignment_current {
            let val = {
                let row = self.tableau.get(&slack).expect("slack row just inserted");
                let mut v = DeltaRational::from_rational(row.constant);
                for (vr, c) in &row.terms {
                    let vi = *vr as usize;
                    if vi < self.assignment.len() {
                        v += self.assignment[vi] * *c;
                    }
                }
                v
            };
            self.assignment[slack as usize] = val;
        }
        slack
    }
    /// Add a constraint: expr >= 0
    pub fn add_ge(&mut self, expr: LinExpr, reason: u32) {
        // expr >= 0  <=>  slack(expr) >= 0.
        let slack = self.intern_row_cached(&expr);
        self.set_lower(slack, Rational64::zero(), reason);
    }
    /// Add a constraint: expr = 0
    pub fn add_eq(&mut self, expr: LinExpr, reason: u32) {
        // expr = 0 as TWO bounds on ONE shared row (not two rows): the row
        // is keyed by the linear form, so both polarities and every
        // re-assertion reuse it.
        let slack = self.intern_row_cached(&expr);
        self.set_lower(slack, Rational64::zero(), reason);
        self.set_upper(slack, Rational64::zero(), reason);
    }
    /// Add a strict constraint: expr < 0
    /// Uses infinitesimals: expr + s = 0 with s > 0
    pub fn add_strict_lt(&mut self, expr: LinExpr, reason: u32) {
        // expr < 0  <=>  slack(expr) < 0 (delta-strict upper bound).
        let slack = self.intern_row_cached(&expr);
        self.set_strict_upper(slack, Rational64::zero(), reason);
    }
    /// Add a strict constraint: expr > 0
    /// Uses infinitesimals: -expr < 0
    pub fn add_strict_gt(&mut self, expr: LinExpr, reason: u32) {
        // expr > 0  <=>  slack(expr) > 0 (delta-strict lower bound).
        let slack = self.intern_row_cached(&expr);
        self.set_strict_lower(slack, Rational64::zero(), reason);
    }
    /// Snapshot the entry assignment and basis for the current decision level
    /// immediately before an operation that may mutate them.  Bounds, fresh
    /// variables and fresh slack rows have explicit undo records, so `push()`
    /// itself remains O(1); only a level that actually runs simplex pays for a
    /// full snapshot, at most once.
    fn ensure_scope_snapshot(&mut self) {
        let Some(index) = self.saved_tableaux.len().checked_sub(1) else {
            return;
        };
        if self.saved_tableaux[index].is_none() {
            self.saved_tableaux[index] = Some((
                self.tableau.clone(),
                self.basic.clone(),
                self.columns.clone(),
            ));
        }
        let Some(index) = self.cached_assignments.len().checked_sub(1) else {
            return;
        };
        if self.cached_assignments[index].is_none() {
            self.cached_assignments[index] = Some(self.assignment.clone());
        }
    }
    /// Eager bound-crossing conflict probe: O(variables), no pivoting.
    ///
    /// Detects a variable whose lower bound exceeds its upper bound
    /// (`x >= a` asserted together with `x <= b`, `a > b`) and returns every
    /// reason backing both bounds.  This is the cheap eager-conflict class
    /// Z3/cvc5 detect at literal-assertion time (asserted-bounds conflict);
    /// the full LP feasibility solve (pivot-based) stays deferred to the
    /// theory `check` at final-check time.  A `Some` result is a sound
    /// refutation of the current bound set; `None` proves nothing (the LP
    /// may still be infeasible – only `check` can tell).
    /// Record a lower>upper crossing on `idx` (if one exists now) with the
    /// FULL antecedents of both bounds, for the next
    /// [`Self::bound_crossing_conflict`] to consume.  See the
    /// `pending_crossing` field's doc for why this is recorded here rather
    /// than scanned for later.
    fn record_crossing(&mut self, idx: usize) {
        if let (Some(lo), Some(hi)) = (&self.lower[idx], &self.upper[idx])
            && lo.value > hi.value
        {
            let mut conflict: Vec<u32> = Vec::new();
            for r in lo.all_reasons().chain(hi.all_reasons()) {
                if !conflict.contains(&r) {
                    conflict.push(r);
                }
            }
            self.pending_crossing = Some(conflict);
        }
    }

    /// The pending bound-crossing conflict, if the most recent bound
    /// assertions created one (see the `pending_crossing` field).  O(1).
    pub fn bound_crossing_conflict(&mut self) -> Option<Vec<u32>> {
        self.pending_crossing.take()
    }

    /// O(variables) scan for any crossed bound pair; the pre-pending version
    /// of [`Self::bound_crossing_conflict`], kept for callers that want a
    /// full sweep (debug assertions, scratch scopes with no probe cadence).
    pub fn scan_bound_crossing_conflict(&self) -> Option<Vec<u32>> {
        for i in 0..self.assignment.len() {
            if let (Some(lo), Some(hi)) = (&self.lower[i], &self.upper[i])
                && lo.value > hi.value
            {
                // Emit ALL antecedents of both crossing bounds, not just their
                // primary reasons: a propagated bound is implied by every
                // reason that fed its derivation, and dropping them yields an
                // incomplete (unsound) conflict explanation.
                let mut conflict: Vec<u32> = Vec::new();
                for r in lo.all_reasons().chain(hi.all_reasons()) {
                    if !conflict.contains(&r) {
                        conflict.push(r);
                    }
                }
                return Some(conflict);
            }
        }
        None
    }

    /// Check if bounds are consistent and restore primal feasibility.
    pub fn check(&mut self) -> Result<(), Vec<u32>> {
        #[cfg(feature = "std")]
        diag::inc_check();
        self.resource_limit = false;
        for i in 0..self.assignment.len() {
            if let (Some(lo), Some(hi)) = (&self.lower[i], &self.upper[i])
                && lo.value > hi.value
            {
                // Emit ALL antecedents of both crossing bounds, not just their
                // primary reasons: a propagated bound is implied by every
                // reason that fed its derivation, and dropping them yields an
                // incomplete (unsound) conflict explanation.
                let mut conflict: Vec<u32> = Vec::new();
                for r in lo.all_reasons().chain(hi.all_reasons()) {
                    if !conflict.contains(&r) {
                        conflict.push(r);
                    }
                }
                return Err(conflict);
            }
        }
        self.ensure_scope_snapshot();
        // Skip the O(tableau) `crash_basis` re-derivation when the assignment
        // is already current (maintained incrementally by `add_le` on basic
        // slacks and left untouched by basic-bound changes).  Non-basic bound
        // changes and `pop` clear the flag, falling back to the full path.
        if !self.assignment_current {
            self.crash_basis();
            self.assignment_current = true;
        }
        self.make_feasible()
    }
    /// Crash basis initialization for faster convergence
    ///
    /// This heuristic initializes the basis to a "good" starting point instead of
    /// starting with all slack variables. It assigns variables to their bounds
    /// based on a heuristic that tries to minimize infeasibilities.
    ///
    /// Benefits:
    /// - Reduces number of pivots needed in Phase I
    /// - Speeds up incremental solving
    /// - Particularly effective when many variables have tight bounds
    ///
    /// Reference: Koberstein's crash procedure for MIP solvers
    fn crash_basis(&mut self) {
        #[cfg(feature = "std")]
        let _t = diag::Timer::new(&diag::CRASH_NS);
        #[cfg(feature = "std")]
        diag::inc_crash();
        for i in 0..self.assignment.len() {
            if i < self.basic.len() && self.basic[i] {
                continue;
            }
            if let Some(lo) = &self.lower[i] {
                self.assignment[i] = lo.value;
            } else if let Some(hi) = &self.upper[i] {
                self.assignment[i] = hi.value;
            } else {
                self.assignment[i] = DeltaRational::zero();
            }
        }
        self.update_assignment();
    }
    /// Pivot to make the solution feasible
    fn make_feasible(&mut self) -> Result<(), Vec<u32>> {
        // Precondition: the assignment is already consistent with the current
        // basis and bounds.  [`Simplex::check`] always runs [`crash_basis`]
        // (which snaps nonbasics to their bounds and calls `update_assignment`)
        // immediately before this, and `make_feasible` is private with no other
        // caller – so recomputing again here was a redundant full pass on every
        // theory check.
        //
        // Degeneration control (Z3 `lp_primal_core_solver`,
        // `one_iteration_tableau_rows`): when the same leaving variable has
        // left the basis more than `BLAND_MODE_THRESHOLD` times in this
        // feasibility pass, switch the entering-variable rule to Bland's for
        // the rest of the pass.  Bland's rule guarantees termination, so the
        // pass can never pivot forever on a degenerate vertex.
        const BLAND_MODE_THRESHOLD: u32 = 1000;
        let mut left_basis_count: FxHashMap<VarId, u32> = FxHashMap::default();
        let mut bland_mode = false;
        for _ in 0..self.max_pivots {
            let violating = self.find_violating();
            if violating.is_none() {
                return Ok(());
            }
            let (basic_var, bound) =
                violating.expect("violating basic variable must exist after is_none check");
            if !bland_mode {
                let repeats = left_basis_count.entry(basic_var).or_insert(0);
                *repeats += 1;
                if *repeats > BLAND_MODE_THRESHOLD {
                    bland_mode = true;
                }
            }
            let pivot_col = if bland_mode {
                self.find_bland_pivot_col(basic_var, &bound)
            } else {
                self.find_pivot_col(basic_var, &bound)
            };
            match pivot_col {
                Some(nonbasic_var) => {
                    #[cfg(feature = "std")]
                    diag::inc_pivot();
                    if !self.pivot(basic_var, nonbasic_var) {
                        return Ok(());
                    }
                }
                None => {
                    return Err(self.explain_conflict(basic_var, &bound));
                }
            }
        }
        self.resource_limit = true;
        Ok(())
    }

    /// Bland's-rule entering choice: the smallest-indexed eligible non-basic
    /// variable in the leaving variable's row (termination-guaranteed).
    fn find_bland_pivot_col(&self, basic_var: VarId, bound: &Bound) -> Option<VarId> {
        let expr = self.tableau.get(&basic_var)?;
        let mut best_var: Option<VarId> = None;
        for (var, coef) in &expr.terms {
            let eligible = match bound.kind {
                BoundType::Lower => {
                    (*coef > Rational64::zero() && self.can_increase(*var))
                        || (*coef < Rational64::zero() && self.can_decrease(*var))
                }
                BoundType::Upper => {
                    (*coef < Rational64::zero() && self.can_increase(*var))
                        || (*coef > Rational64::zero() && self.can_decrease(*var))
                }
                _ => false,
            };
            if eligible && best_var.is_none_or(|cur| *var < cur) {
                best_var = Some(*var);
            }
        }
        best_var
    }
    /// Dual Simplex: Restore primal feasibility while maintaining dual feasibility
    ///
    /// The dual simplex algorithm is particularly efficient when:
    /// - After adding cuts in branch-and-bound (cuts make primal infeasible but dual stays feasible)
    /// - When resolving from a previously optimal basis after bound changes
    /// - For incremental solving where the problem structure changes slightly
    ///
    /// Unlike primal simplex which maintains primal feasibility and seeks optimality,
    /// dual simplex maintains dual feasibility (optimal reduced costs) and seeks primal feasibility.
    ///
    /// This is often faster than primal simplex after adding cutting planes because:
    /// - The dual remains feasible after most cuts
    /// - Only a few pivots are needed to restore primal feasibility
    /// - Warm-starting from the previous optimal basis is very effective
    ///
    /// Reference:
    /// - Dantzig, "Linear Programming and Extensions" (1963), Chapter 7
    /// - Bixby, "Implementing the Simplex Method" (2002)
    /// - Modern MIP solvers (CPLEX, Gurobi) use dual simplex as the primary LP solver
    pub fn dual_simplex(&mut self) -> Result<(), Vec<u32>> {
        self.ensure_scope_snapshot();
        self.resource_limit = false;
        self.update_assignment();
        for _ in 0..self.max_pivots {
            let violating = self.find_violating();
            if violating.is_none() {
                return Ok(());
            }
            let (leaving_var, bound) =
                violating.expect("violating basic variable must exist after is_none check");
            let entering = self.find_dual_pivot_col(leaving_var, &bound);
            match entering {
                Some(entering_var) => {
                    if !self.pivot(leaving_var, entering_var) {
                        return Ok(());
                    }
                }
                None => {
                    return Err(self.explain_conflict(leaving_var, &bound));
                }
            }
        }
        self.resource_limit = true;
        Ok(())
    }
    /// Find entering variable for dual simplex (maintains dual feasibility)
    ///
    /// Given a leaving variable (basic var violating bounds), find a non-basic variable
    /// to enter the basis such that:
    /// 1. The pivot reduces the bound violation
    /// 2. Dual feasibility is maintained (reduced costs stay optimal)
    ///
    /// For leaving variable x_i with row: x_i = c + sum(a_j * x_j)
    ///
    /// If x_i < lower_i (too small):
    /// - Need to increase x_i
    /// - Choose x_j with a_j > 0 (increases x_i) and can increase
    /// - Or x_j with a_j < 0 (decreases moves x_i up) and can decrease
    ///
    /// If x_i > upper_i (too large):
    /// - Need to decrease x_i
    /// - Choose x_j with a_j < 0 (increases x_j decreases x_i) and can increase
    /// - Or x_j with a_j > 0 (decreases x_j decreases x_i) and can decrease
    ///
    /// Among eligible variables, choose the one that maintains dual feasibility.
    /// This typically means choosing the variable with the smallest ratio of:
    /// (change in objective) / (change in constraint violation)
    ///
    /// For now, we use a simple rule: choose the first eligible variable (Bland's rule for dual)
    #[allow(dead_code)]
    fn find_dual_pivot_col(&self, leaving_var: VarId, bound: &Bound) -> Option<VarId> {
        let expr = self.tableau.get(&leaving_var)?;
        let mut best_var = None;
        for (var, coef) in &expr.terms {
            let can_increase = self.can_increase(*var);
            let can_decrease = self.can_decrease(*var);
            let is_eligible = match bound.kind {
                BoundType::Lower => {
                    (*coef > Rational64::zero() && can_increase)
                        || (*coef < Rational64::zero() && can_decrease)
                }
                BoundType::Upper => {
                    (*coef < Rational64::zero() && can_increase)
                        || (*coef > Rational64::zero() && can_decrease)
                }
                _ => false,
            };
            if is_eligible {
                best_var = match best_var {
                    None => Some(*var),
                    Some(current) if *var < current => Some(*var),
                    Some(current) => Some(current),
                };
            }
        }
        best_var
    }
    /// Find a basic variable that violates its bounds
    /// Find the smallest-indexed basic variable violating a bound.
    ///
    /// Z3's `find_smallest_inf_column` (see
    /// `lp_primal_core_solver.h::one_iteration_tableau_rows`): the leaving
    /// variable is the *smallest-indexed* infeasible basic column, so the
    /// pivot sequence is deterministic (independent of hash iteration order)
    /// and degenerate repeats are easy to detect for the Bland-mode switch.
    fn find_violating(&self) -> Option<(VarId, Bound)> {
        let mut worst: Option<(VarId, Bound)> = None;
        for var in self.tableau.keys() {
            let idx = *var as usize;
            let val = self.assignment[idx];
            let viol = if let Some(lo) = &self.lower[idx]
                && val < lo.value
            {
                Some(lo.clone())
            } else if let Some(hi) = &self.upper[idx]
                && val > hi.value
            {
                Some(hi.clone())
            } else {
                None
            };
            if let Some(bound) = viol
                && worst.as_ref().is_none_or(|(v, _)| *var < *v)
            {
                worst = Some((*var, bound));
            }
        }
        worst
    }
    /// Find the entering (non-basic) variable for one feasibility pivot.
    ///
    /// Z3's `find_beneficial_entering_tableau_rows`
    /// (`lp_primal_core_solver.h`): among the eligible non-basic variables in
    /// the leaving variable's row, prefer the one that keeps the tableau
    /// sparse – score by (number of *non-free* basic dependents, column
    /// length), minimum wins, ties broken by the smaller variable id.  Short
    /// columns make every later pivot touch fewer rows, and non-free (bounded)
    /// dependents cannot absorb arbitrary value changes, so entering a column
    /// full of them immediately recreates infeasibility elsewhere.
    fn find_pivot_col(&self, basic_var: VarId, bound: &Bound) -> Option<VarId> {
        let expr = self.tableau.get(&basic_var)?;
        // (non-free dependents, column length, variable) – smaller is better.
        let mut best: Option<(usize, usize, VarId)> = None;
        for (var, coef) in &expr.terms {
            let is_eligible = match bound.kind {
                BoundType::Lower => {
                    (*coef > Rational64::zero() && self.can_increase(*var))
                        || (*coef < Rational64::zero() && self.can_decrease(*var))
                }
                BoundType::Upper => {
                    (*coef < Rational64::zero() && self.can_increase(*var))
                        || (*coef > Rational64::zero() && self.can_decrease(*var))
                }
                _ => false,
            };
            if !is_eligible {
                continue;
            }
            let non_free_deps = self.num_nonfree_basic_dependents(*var, best.map(|b| b.0));
            let col_len = self.columns.get(var).map_or(0usize, |c| c.len());
            let better =
                best.is_none_or(|(bd, bl, bv)| (non_free_deps, col_len, *var) < (bd, bl, bv));
            if better {
                best = Some((non_free_deps, col_len, *var));
            }
        }
        best.map(|(_, _, v)| v)
    }

    /// Number of *non-free* basic variables (capped at `cap + 1`) whose
    /// tableau rows reference `var` – Z3's
    /// `get_num_of_not_free_basic_dependent_vars`.  "Non-free" = carries at
    /// least one finite bound; a free basic dependent absorbs any value
    /// change without becoming infeasible, so it does not count against the
    /// candidate.
    fn num_nonfree_basic_dependents(&self, var: VarId, cap: Option<usize>) -> usize {
        let Some(col) = self.columns.get(&var) else {
            return 0;
        };
        let limit = cap.map_or(usize::MAX, |c| c.saturating_add(1));
        let mut count = 0usize;
        for &row in col.iter() {
            let idx = row as usize;
            if idx < self.lower.len() && (self.lower[idx].is_some() || self.upper[idx].is_some()) {
                count += 1;
                if count >= limit {
                    break;
                }
            }
        }
        count
    }

    /// Check if a variable can be increased
    #[inline]
    pub(super) fn can_increase(&self, var: VarId) -> bool {
        let idx = var as usize;
        match &self.upper[idx] {
            Some(hi) => self.assignment[idx] < hi.value,
            None => true,
        }
    }
    /// Check if a variable can be decreased
    #[inline]
    pub(super) fn can_decrease(&self, var: VarId) -> bool {
        let idx = var as usize;
        match &self.lower[idx] {
            Some(lo) => self.assignment[idx] > lo.value,
            None => true,
        }
    }
    /// Perform a pivot operation.
    ///
    /// `Rational64` is `i64`-backed: repeated pivoting can grow numerators
    /// and denominators without bound (the classic fraction-free-elimination
    /// blowup), and `num-rational`'s arithmetic operators do not check for
    /// overflow -- they panic in debug builds and silently wrap to a wrong
    /// coefficient in release builds. To avoid both, every coefficient
    /// computed here goes through the `checked_*_r64` helpers, and the pivot
    /// is fully validated (via a `i128`-checked dry run) BEFORE any tableau
    /// state is mutated: an overflow anywhere aborts the pivot with no
    /// partial mutation, matching the pre-existing `resource_limit` "give up
    /// honestly" contract used for pivot-budget exhaustion. Returns `false`
    /// iff the pivot could not be completed (overflow, or a broken tableau
    /// invariant), in which case `resource_limit` is set so callers report
    /// `Unknown` rather than trusting a fabricated/partial result.
    ///
    /// Not `#[must_use]`: `simplex_opt.rs`'s optimization-direction pivot
    /// loop currently ignores the outcome (pre-existing behavior, out of
    /// this module's scope to change) and relies on the subsequent
    /// pivot-budget/optimality bookkeeping to notice a stalled search.
    pub(super) fn pivot(&mut self, basic_var: VarId, nonbasic_var: VarId) -> bool {
        #[cfg(feature = "profiling")]
        let _timer = ScopedTimer::new(ProfilingCategory::SimplexPivot);
        self.ensure_scope_snapshot();
        let Some(expr) = self.tableau.get(&basic_var) else {
            self.resource_limit = true;
            return false;
        };
        let Some(coef) = expr
            .terms
            .iter()
            .find(|(v, _)| *v == nonbasic_var)
            .map(|(_, c)| *c)
        else {
            self.resource_limit = true;
            return false;
        };
        let Some(inv_coef) = checked_recip_r64(coef) else {
            self.resource_limit = true;
            return false;
        };
        let Some(new_constant) =
            checked_neg_r64(expr.constant).and_then(|n| checked_div_r64(n, coef))
        else {
            self.resource_limit = true;
            return false;
        };
        let mut new_expr = LinExpr::new();
        new_expr.terms.push((basic_var, inv_coef));
        new_expr.constant = new_constant;
        for (var, c) in &expr.terms {
            if *var != nonbasic_var {
                let Some(neg_c) = checked_neg_r64(*c) else {
                    self.resource_limit = true;
                    return false;
                };
                let Some(val) = checked_div_r64(neg_c, coef) else {
                    self.resource_limit = true;
                    return false;
                };
                if !new_expr.try_add_term(*var, val) {
                    self.resource_limit = true;
                    return false;
                }
            }
        }
        // Collect the rows that reference the entering column – in O(column)
        // via the column index rather than a full-tableau scan – and compute
        // their substituted content into `row_updates` WITHOUT mutating the
        // tableau: every coefficient goes through the checked rational
        // helpers, and an overflow anywhere aborts the pivot with NO partial
        // mutation (the transactional validate-then-commit contract callers
        // and the overflow regression test rely on).
        let mut row_updates: Vec<(VarId, LinExpr)> = Vec::new();
        if let Some(col) = self.columns.get(&nonbasic_var).cloned() {
            for &var in col.iter() {
                if var == basic_var {
                    continue;
                }
                let Some((sc, row)) = self.tableau.get(&var).and_then(|row| {
                    row.terms
                        .iter()
                        .find(|(v, _)| *v == nonbasic_var)
                        .map(|(_, c)| (*c, row.clone()))
                }) else {
                    continue;
                };
                let mut new_row = (*row).clone();
                new_row.terms.retain(|(v, _)| *v != nonbasic_var);
                let Some(delta_c) = checked_mul_r64(sc, new_expr.constant) else {
                    self.resource_limit = true;
                    return false;
                };
                let Some(sum) = checked_add_r64(new_row.constant, delta_c) else {
                    self.resource_limit = true;
                    return false;
                };
                new_row.constant = sum;
                for (v, c) in &new_expr.terms {
                    if !new_row.try_add_term_mul(*v, sc, *c) {
                        self.resource_limit = true;
                        return false;
                    }
                }
                row_updates.push((var, new_row));
            }
        }
        // Targeted assignment update.  After a pivot the *only* variable
        // whose value changes is `basic_var` (it leaves the basis and is
        // snapped to a bound); every other nonbasic keeps its value, so a
        // basic variable's assignment changes only if its (new) row references
        // `basic_var`.  Those are exactly the entering variable's new row
        // (`new_expr`) and the rows just rewritten by substitution
        // (`row_updates`).  Recomputing every basic – as the old full
        // `update_assignment()` did – was pure waste and the dominant cost:
        // ~40-52% of QF_UFLIA runtime was `Ratio::mul`/`reduce` driven by that
        // per-pivot full re-evaluation.
        let leaving = basic_var as usize;
        let mut snap_delta: Option<DeltaRational> = None;
        if leaving < self.assignment.len() {
            // Snap the now-nonbasic leaving var to a bound, matching
            // `update_assignment`'s lower-preferred rule.
            let snapped = self
                .lower
                .get(leaving)
                .and_then(|o| o.as_ref())
                .map(|b| b.value)
                .or_else(|| {
                    self.upper
                        .get(leaving)
                        .and_then(|o| o.as_ref())
                        .map(|b| b.value)
                });
            if let Some(v) = snapped {
                let old = self.assignment[leaving];
                if v != old {
                    snap_delta = Some(v - old);
                }
                self.assignment[leaving] = v;
            }
        }
        let entering = nonbasic_var as usize;
        if entering < self.assignment.len()
            && let Some(v) = self.eval_expr(&new_expr)
        {
            self.assignment[entering] = v;
        }
        // Update the edited rows' basic variables by DELTA propagation
        // instead of re-evaluating each row.  A substituted row is the same
        // linear function of the same original variables, so at the pre-snap
        // point its value is unchanged; the only input that moved is the
        // snapped `basic_var`, so `value += Δ · coef(basic_var in new_row)` –
        // one multiply-add per row – reproduces `eval_expr(new_row)` exactly
        // (exact rationals: no rounding) at a fraction of the pivots' cost
        // (the full re-evaluation was the top arithmetic consumer on dense
        // CAV/QF_LIA rows).
        if let Some(delta) = snap_delta {
            for (var, new_row) in &row_updates {
                let vi = *var as usize;
                if vi >= self.assignment.len() {
                    continue;
                }
                if let Some(coef) = new_row
                    .terms
                    .iter()
                    .find(|(v, _)| *v == basic_var)
                    .map(|(_, c)| *c)
                {
                    // Checked delta arithmetic: a silent overflow here would
                    // corrupt every later decision built on this assignment.
                    if let Some(d) = checked_mul_delta(delta, coef)
                        && let Some(sum) = checked_add_delta(self.assignment[vi], d)
                    {
                        #[cfg(debug_assertions)]
                        {
                            let want = self.eval_expr(new_row);
                            debug_assert!(
                                want.is_none_or(|w| w == sum),
                                "delta propagation mismatch: delta={delta:?} coef={coef:?} got={sum:?} want={want:?}"
                            );
                        }
                        self.assignment[vi] = sum;
                    } else {
                        // Overflow: refuse to guess a value.  Mark the
                        // assignment stale so the next `check()` re-derives
                        // everything from the tableau.
                        self.assignment_current = false;
                    }
                }
            }
        }

        // Column index maintenance: the leaving variable's row is gone, the
        // entering variable gained a row, the edited rows dropped their
        // reference to the entering variable and gained ones to the leaving
        // variable (plus any other term `new_expr` substituted in).
        if let Some(old_row) = self.tableau.get(&basic_var) {
            let old_terms: SmallVec<[VarId; 4]> = old_row.terms.iter().map(|(v, _)| *v).collect();
            for v in old_terms {
                // Exact column index + basic row ⇒ `v`'s column holds
                // `basic_var` exactly once; drop without the position scan.
                self.column_drop_known(v, basic_var);
            }
        }
        self.tableau.remove(&basic_var);
        let entering_terms: SmallVec<[VarId; 4]> = new_expr.terms.iter().map(|(v, _)| *v).collect();
        self.tableau.insert(nonbasic_var, Arc::new(new_expr));
        for v in entering_terms {
            // The entering variable had no row before, so no column listed it
            // as a row owner; push without the membership scan.  (Terms it
            // references may already list OTHER rows – that is a different
            // key, untouched here.)
            self.column_push_known(v, nonbasic_var);
        }
        // Commit the substituted rows and maintain their column entries.
        // Substitution merges `new_expr` into the old row term-by-term, and a
        // merge can CANCEL a coefficient to zero – so the new row's term set
        // must be diffed against the old one in full, not just the entering
        // column removed (a stale `columns[v]` entry for a cancelled term made
        // `on_nonbasic_bound_change` skip real dependents and let later edits
        // miss rows entirely: corrupted tableau, wrong answers).
        for (var, new_row) in row_updates {
            // Diff-based column maintenance: the column index is exact, so a
            // term present in both rows needs no touch, a dropped term needs
            // removal, and an added term is guaranteed absent from the column
            // (direct push – `column_add`'s membership scan over dense
            // columns was a top profiler entry here).
            let (dropped, added): (SmallVec<[VarId; 4]>, SmallVec<[VarId; 4]>) =
                match self.tableau.get(&var) {
                    Some(old_row) => {
                        let mut dropped = SmallVec::new();
                        for (v, _) in old_row.terms.iter() {
                            if !new_row.terms.iter().any(|(nv, _)| nv == v) {
                                dropped.push(*v);
                            }
                        }
                        let mut added = SmallVec::new();
                        for (v, _) in new_row.terms.iter() {
                            if !old_row.terms.iter().any(|(nv, _)| nv == v) {
                                added.push(*v);
                            }
                        }
                        (dropped, added)
                    }
                    None => (SmallVec::new(), SmallVec::new()),
                };
            for v in dropped {
                self.column_drop_known(v, var);
            }
            for v in added {
                // Exactness invariant: `v` was not in this row, so the column
                // cannot list `var` under `v` yet.
                self.column_push_known(v, var);
            }
            self.tableau.insert(var, Arc::new(new_row));
        }
        self.basic[basic_var as usize] = false;
        self.basic[nonbasic_var as usize] = true;
        #[cfg(debug_assertions)]
        self.debug_verify_columns();
        true
    }

    /// Verify `columns` is an exact index of the tableau (debug builds only:
    /// O(tableau·terms) per pivot).
    #[cfg(debug_assertions)]
    fn debug_verify_columns(&self) {
        for (var, row) in &self.tableau {
            for (t, _) in &row.terms {
                debug_assert!(
                    self.columns.get(t).is_some_and(|c| c.contains(var)),
                    "columns[{t}] missing row {var} that references it"
                );
            }
        }
        for (t, col) in &self.columns {
            for r in col.iter() {
                debug_assert!(
                    self.tableau
                        .get(r)
                        .is_some_and(|row| row.terms.iter().any(|(v, _)| v == t)),
                    "columns[{t}] lists row {r} which does not reference it"
                );
            }
        }
    }
    /// Evaluate a tableau row at the current nonbasic assignment.
    ///
    /// Returns `None` if the row references a stale (out-of-range) variable,
    /// in which case the caller leaves that basic variable's assignment
    /// untouched – matching [`Simplex::update_assignment`]'s `has_stale_ref`
    /// skip, so targeted updates stay consistent with the full recompute.
    fn eval_expr(&self, expr: &LinExpr) -> Option<DeltaRational> {
        let num_vars = self.assignment.len();
        let mut val = DeltaRational::from_rational(expr.constant);
        for (v, c) in &expr.terms {
            let idx = *v as usize;
            if idx >= num_vars {
                return None;
            }
            val += self.assignment[idx] * *c;
        }
        Some(val)
    }
    /// Update variable assignments after pivot
    pub(super) fn update_assignment(&mut self) {
        let num_vars = self.assignment.len();
        for i in 0..num_vars {
            if !self.basic[i] {
                if let Some(lo) = &self.lower[i] {
                    self.assignment[i] = lo.value;
                } else if let Some(hi) = &self.upper[i] {
                    self.assignment[i] = hi.value;
                }
            }
        }
        for (var, expr) in &self.tableau {
            let var_idx = *var as usize;
            if var_idx >= num_vars {
                continue;
            }
            let mut val = DeltaRational::from_rational(expr.constant);
            let mut has_stale_ref = false;
            for (v, c) in &expr.terms {
                let v_idx = *v as usize;
                if v_idx >= num_vars {
                    has_stale_ref = true;
                    break;
                }
                val += self.assignment[v_idx] * *c;
            }
            if !has_stale_ref {
                self.assignment[var_idx] = val;
            }
        }
    }
    /// Explain why a conflict occurred using Farkas lemma
    ///
    /// When a basic variable x_i violates its bounds and no pivot is possible,
    /// we can derive a conflict clause from the bounds of all involved variables.
    ///
    /// For x_i = c + sum(a_j * x_j):
    /// - If x_i < lower(x_i), we need to explain why x_i can't reach its lower bound
    /// - If x_i > upper(x_i), we need to explain why x_i can't decrease to its upper bound
    ///
    /// The conflict clause contains the reasons for all the bounds that prevent a pivot.
    fn explain_conflict(&self, basic_var: VarId, bound: &Bound) -> Vec<u32> {
        let mut reasons: Vec<u32> = Vec::new();
        // Every antecedent of the violated bound (primary + auxiliary), so a
        // propagated bound contributes all of the reasons that derived it.
        let push_all = |b: &Bound, reasons: &mut Vec<u32>| {
            for r in b.all_reasons() {
                if !reasons.contains(&r) {
                    reasons.push(r);
                }
            }
        };
        push_all(bound, &mut reasons);
        let expr = match self.tableau.get(&basic_var) {
            Some(e) => e,
            None => return reasons,
        };
        for (var, coef) in &expr.terms {
            let var_idx = *var as usize;
            match bound.kind {
                BoundType::Lower => {
                    if *coef > Rational64::zero()
                        && let Some(hi) = &self.upper[var_idx]
                    {
                        push_all(hi, &mut reasons);
                    } else if *coef < Rational64::zero()
                        && let Some(lo) = &self.lower[var_idx]
                    {
                        push_all(lo, &mut reasons);
                    }
                }
                BoundType::Upper => {
                    if *coef > Rational64::zero()
                        && let Some(lo) = &self.lower[var_idx]
                    {
                        push_all(lo, &mut reasons);
                    } else if *coef < Rational64::zero()
                        && let Some(hi) = &self.upper[var_idx]
                    {
                        push_all(hi, &mut reasons);
                    }
                }
                _ => {}
            }
        }
        reasons
    }
    /// Perform bound propagation through the tableau
    ///
    /// For each basic variable x_i = c + sum(a_j * x_j), we can derive bounds:
    /// - If all x_j have bounds, we can compute bounds for x_i
    /// - If x_i has a bound, we may derive bounds for x_j
    pub fn propagate_bounds(&mut self) {
        self.propagated.clear();
        for (basic_var, expr) in &self.tableau {
            if let Some(bound) = self.derive_basic_bound(*basic_var, expr) {
                self.propagated.push(bound);
            }
        }
        let props = self.propagated.clone();
        for prop in &props {
            let idx = prop.var as usize;
            if idx >= self.lower.len() {
                continue;
            }
            if prop.reasons.is_empty() {
                continue;
            }
            if prop.is_lower {
                let should_update = match &self.lower[idx] {
                    None => true,
                    Some(existing) => prop.value > existing.value,
                };
                if should_update {
                    self.set_lower_delta(prop.var, prop.value, prop.reasons.clone());
                }
            } else {
                let should_update = match &self.upper[idx] {
                    None => true,
                    Some(existing) => prop.value < existing.value,
                };
                if should_update {
                    self.set_upper_delta(prop.var, prop.value, prop.reasons.clone());
                }
            }
        }
    }
    /// Derive bounds for a basic variable from bounds on non-basic variables
    ///
    /// For basic variable x_i = c + sum(a_j * x_j):
    /// - Lower bound: sum of (a_j * lower(x_j) if a_j > 0, a_j * upper(x_j) if a_j < 0)
    /// - Upper bound: sum of (a_j * upper(x_j) if a_j > 0, a_j * lower(x_j) if a_j < 0)
    fn derive_basic_bound(&self, basic_var: VarId, expr: &LinExpr) -> Option<PropagatedBound> {
        let idx = basic_var as usize;
        let mut lower_sum = DeltaRational::from_rational(expr.constant);
        let mut lower_reasons: SmallVec<[u32; 4]> = SmallVec::new();
        let mut can_derive_lower = true;
        for (var, coef) in &expr.terms {
            let var_idx = *var as usize;
            if *coef > Rational64::zero() {
                if let Some(lo) = &self.lower[var_idx] {
                    lower_sum += lo.value * *coef;
                    // Carry EVERY antecedent of this bound (primary + auxiliary),
                    // not just its primary reason: when `lo` is itself a
                    // propagated bound derived from several reasons, dropping its
                    // `aux_reasons` here would yield an incomplete conflict
                    // explanation one derivation step later. `split_reasons`
                    // deduplicates downstream.
                    lower_reasons.extend(lo.all_reasons());
                } else {
                    can_derive_lower = false;
                    break;
                }
            } else {
                if let Some(hi) = &self.upper[var_idx] {
                    lower_sum += hi.value * *coef;
                    lower_reasons.extend(hi.all_reasons());
                } else {
                    can_derive_lower = false;
                    break;
                }
            }
        }
        if can_derive_lower {
            let is_tighter = match &self.lower[idx] {
                None => true,
                Some(existing) => lower_sum > existing.value,
            };
            if is_tighter {
                return Some(PropagatedBound {
                    var: basic_var,
                    is_lower: true,
                    value: lower_sum,
                    reasons: lower_reasons,
                });
            }
        }
        let mut upper_sum = DeltaRational::from_rational(expr.constant);
        let mut upper_reasons: SmallVec<[u32; 4]> = SmallVec::new();
        let mut can_derive_upper = true;
        for (var, coef) in &expr.terms {
            let var_idx = *var as usize;
            if *coef > Rational64::zero() {
                if let Some(hi) = &self.upper[var_idx] {
                    upper_sum += hi.value * *coef;
                    upper_reasons.extend(hi.all_reasons());
                } else {
                    can_derive_upper = false;
                    break;
                }
            } else {
                if let Some(lo) = &self.lower[var_idx] {
                    upper_sum += lo.value * *coef;
                    upper_reasons.extend(lo.all_reasons());
                } else {
                    can_derive_upper = false;
                    break;
                }
            }
        }
        if can_derive_upper {
            let is_tighter = match &self.upper[idx] {
                None => true,
                Some(existing) => upper_sum < existing.value,
            };
            if is_tighter {
                return Some(PropagatedBound {
                    var: basic_var,
                    is_lower: false,
                    value: upper_sum,
                    reasons: upper_reasons,
                });
            }
        }
        None
    }
    /// Get pending propagated bounds
    #[must_use]
    pub fn get_propagated(&self) -> &[PropagatedBound] {
        &self.propagated
    }
    /// Clear propagated bounds
    pub fn clear_propagated(&mut self) {
        self.propagated.clear();
    }
    /// Tighten bounds on a variable if possible
    /// Returns true if bounds were tightened
    ///
    /// Like [`Self::propagate_bounds`] (see its doc comment for the full
    /// rationale), this routes writes through the undo trail via
    /// `set_lower_delta`/`set_upper_delta` rather than writing
    /// `self.lower`/`self.upper` directly, and skips applying a derived
    /// bound with no recorded reason rather than fabricating one.
    pub fn tighten_bounds(&mut self, var: VarId) -> bool {
        let idx = var as usize;
        let mut changed = false;
        if let Some(expr) = self.tableau.get(&var).cloned()
            && let Some(prop) = self.derive_basic_bound(var, &expr)
            && !prop.reasons.is_empty()
        {
            if prop.is_lower {
                let should_update = match &self.lower[idx] {
                    None => true,
                    Some(existing) => prop.value > existing.value,
                };
                if should_update {
                    self.set_lower_delta(var, prop.value, prop.reasons.clone());
                    changed = true;
                }
            } else {
                let should_update = match &self.upper[idx] {
                    None => true,
                    Some(existing) => prop.value < existing.value,
                };
                if should_update {
                    self.set_upper_delta(var, prop.value, prop.reasons.clone());
                    changed = true;
                }
            }
        }
        changed
    }
    /// Get the number of original (non-slack) variables
    #[must_use]
    pub fn num_original_vars(&self) -> usize {
        self.num_vars
    }
    /// Get lower bound of a variable (if any)
    #[must_use]
    pub fn get_lower(&self, var: VarId) -> Option<&Bound> {
        self.lower.get(var as usize).and_then(|b| b.as_ref())
    }
    /// Get upper bound of a variable (if any)
    #[must_use]
    pub fn get_upper(&self, var: VarId) -> Option<&Bound> {
        self.upper.get(var as usize).and_then(|b| b.as_ref())
    }
    /// Reset the solver
    pub fn reset(&mut self) {
        self.num_vars = 0;
        self.num_slack = 0;
        self.assignment.clear();
        self.lower.clear();
        self.upper.clear();
        self.tableau.clear();
        self.columns.clear();
        self.row_ids.clear();
        self.row_scope_trail.clear();
        self.row_scope_marks = vec![0];
        self.basic.clear();
        self.infeasible = None;
        self.propagated.clear();
        self.trail.clear();
        self.trail_limits.clear();
        self.trail_limits.push(0);
        self.cached_assignments.clear();
        self.saved_tableaux.clear();
        self.resource_limit = false;
        self.assignment_current = true;
    }
    /// Current decision-level depth of the bound trail (number of live push
    /// scopes); `0` at the assertion/base level.
    #[must_use]
    pub fn scope_depth(&self) -> usize {
        self.trail_limits.len().saturating_sub(1)
    }

    /// Pop the bound trail back to the assertion/base level (scope 0),
    /// discarding every decision-level bound.  Used by optimisation queries
    /// that must range over the *asserted* constraints alone (see
    /// `ArithSolver::lp_int_bounds`).
    pub fn pop_to_base(&mut self) {
        while self.scope_depth() > 0 {
            self.pop();
        }
    }

    /// Push a new decision level
    pub fn push(&mut self) {
        self.trail_limits.push(self.trail.len());
        self.cached_assignments.push(None);
        self.saved_tableaux.push(None);
    }
    /// Pop to previous decision level.
    ///
    /// With search-global rows/variables (see `register_var`/`new_slack`),
    /// a pop only has to replay the BOUND undo trail: rows constrain
    /// nothing without their bounds, the basis is free to remain pivoted
    /// (any basis spanning the row space is valid), and the assignment is
    /// conservatively marked stale (`assignment_current = false`) so the
    /// next `check` re-derives it via `crash_basis`.  This is the
    /// Dutertre–de Moura backtracking contract: bounds are the only
    /// backtrackable state.
    pub fn pop(&mut self) {
        // A pending crossing was recorded under the scope being popped: its
        // asserting literals are gone, so blaming them in a later probe would
        // cite literals the SAT core no longer holds assigned.
        self.pending_crossing = None;
        // Dutertre–de-Moura backtracking contract: ONLY bounds are
        // backtrackable.  Rows are permanent, content-addressed definitions
        // (`intern_row_cached`) – a row without bounds constrains nothing, so
        // its bounds dying at this pop fully retracts the scope's
        // assertions.  The basis is free to stay pivoted (any basis spanning
        // the row space is valid); the assignment is restored from the scope
        // snapshot below.
        let saved_tableau = self.saved_tableaux.pop().flatten();
        let cached_assignment = self.cached_assignments.pop().flatten();
        if let Some((saved_tableau, mut saved_basic, saved_columns)) = saved_tableau {
            saved_basic.resize(self.basic.len(), false);
            self.basic = saved_basic;
            self.tableau = saved_tableau;
            self.columns = saved_columns;
        }
        if let Some(limit) = self.trail_limits.pop() {
            while self.trail.len() > limit {
                if let Some(undo) = self.trail.pop() {
                    match undo {
                        BoundUndo::LowerWasNone(var) => {
                            self.lower[var as usize] = None;
                        }
                        BoundUndo::LowerWasSome(var, old) => {
                            self.lower[var as usize] = Some(old);
                        }
                        BoundUndo::UpperWasNone(var) => {
                            self.upper[var as usize] = None;
                        }
                        BoundUndo::UpperWasSome(var, old) => {
                            self.upper[var as usize] = Some(old);
                        }
                    }
                }
            }
            if let Some(cached) = cached_assignment {
                let restore_len = cached.len().min(self.assignment.len());
                self.assignment[..restore_len].copy_from_slice(&cached[..restore_len]);
                for item in self.assignment.iter_mut().skip(restore_len) {
                    *item = DeltaRational::zero();
                }
                // Variables created inside this scope (rows are permanent, so
                // their slacks live on as BASIC vars with rows but no
                // bounds) now hold zeroed assignments that do NOT satisfy
                // their rows.  The next `check` must re-derive the basic
                // assignments via `crash_basis` instead of trusting the
                // incremental flag.
                if self.assignment.len() > restore_len {
                    self.assignment_current = false;
                }
            }
            self.infeasible = None;
        }
    }
    /// Get the current decision level
    #[must_use]
    pub fn decision_level(&self) -> usize {
        self.trail_limits.len().saturating_sub(1)
    }
    /// Number of allocated variable slots (original + slack).
    #[inline]
    pub(super) fn assignment_len(&self) -> usize {
        self.assignment.len()
    }
    /// Real-part of the assignment at index `idx`.
    #[inline]
    pub(super) fn assignment_real_at(&self, idx: usize) -> Rational64 {
        self.assignment[idx].real
    }
    /// Full `DeltaRational` assignment at index `idx`.
    #[inline]
    pub(super) fn assignment_at(&self, idx: usize) -> Rational64 {
        self.assignment[idx].real
    }
    /// Whether variable at `idx` is currently basic.
    #[inline]
    pub(super) fn is_basic(&self, idx: usize) -> bool {
        idx < self.basic.len() && self.basic[idx]
    }

    /// Whether `var` currently carries a defining row in the tableau.
    ///
    /// A slack is basic exactly while its defining row exists: pivoting it
    /// out REMOVES the row.  Content-addressed row caches must consult this
    /// before reusing a slack – a cached slack that left the basis no longer
    /// equals its linear form, and a bound set on it would constrain a
    /// free-floating variable instead of the form (silently dropping the
    /// constraint).
    #[inline]
    #[must_use]
    pub fn row_defines_var(&self, var: VarId) -> bool {
        self.tableau.contains_key(&var)
    }
    /// A bound changed.  Basic variables' assignments are tableau-derived, so
    /// nothing moves; a non-basic variable's assignment snaps into its new
    /// bound window and the delta propagates to exactly the rows in its
    /// column ([`Self::on_nonbasic_bound_change`]).
    fn note_bound_change(&mut self, idx: usize) {
        self.on_nonbasic_bound_change(idx);
    }
    /// Iterate over `(basic_var, row)` pairs in the tableau.
    pub(super) fn tableau_iter(&self) -> impl Iterator<Item = (&VarId, &LinExpr)> {
        self.tableau.iter().map(|(v, row)| (v, row.as_ref()))
    }
    /// Iterate over basic variable IDs in the tableau.
    pub(super) fn tableau_keys(&self) -> impl Iterator<Item = VarId> + '_ {
        self.tableau.keys().copied()
    }
    /// Return the coefficient of `nonbasic` in the row of `basic`, or `None`.
    pub(super) fn tableau_coef_of(&self, basic: VarId, nonbasic: VarId) -> Option<Rational64> {
        self.tableau.get(&basic).and_then(|row| {
            row.terms
                .iter()
                .find(|(v, _)| *v == nonbasic)
                .map(|(_, c)| *c)
        })
    }
    /// Full lower bound (with reasons) for variable at `idx`, if any.
    /// Used by the Gomory-cut generator, which needs the bound's *reasons*
    /// to justify the cut as a consequence of the asserted atoms.
    #[inline]
    pub(super) fn bound_lower_at(&self, idx: usize) -> Option<&Bound> {
        self.lower.get(idx).and_then(|b| b.as_ref())
    }
    /// Full upper bound (with reasons); see [`Self::bound_lower_at`].
    #[inline]
    pub(super) fn bound_upper_at(&self, idx: usize) -> Option<&Bound> {
        self.upper.get(idx).and_then(|b| b.as_ref())
    }
    /// Real part of the upper bound for variable at `idx`, if any.
    #[inline]
    pub(super) fn upper_real_at(&self, idx: usize) -> Option<Rational64> {
        self.upper
            .get(idx)
            .and_then(|b| b.as_ref().map(|b| b.value.real))
    }
    /// Real part of the lower bound for variable at `idx`, if any.
    #[inline]
    pub(super) fn lower_real_at(&self, idx: usize) -> Option<Rational64> {
        self.lower
            .get(idx)
            .and_then(|b| b.as_ref().map(|b| b.value.real))
    }
    /// Full `DeltaRational` upper bound for variable at `idx`, if any.
    #[inline]
    pub(super) fn upper_delta_at(&self, idx: usize) -> Option<DeltaRational> {
        self.upper
            .get(idx)
            .and_then(|b| b.as_ref().map(|b| b.value))
    }
    /// Full `DeltaRational` lower bound for variable at `idx`, if any.
    #[inline]
    pub(super) fn lower_delta_at(&self, idx: usize) -> Option<DeltaRational> {
        self.lower
            .get(idx)
            .and_then(|b| b.as_ref().map(|b| b.value))
    }
    /// Overwrite the assignment at `idx` with `val`.
    #[inline]
    pub(super) fn set_assignment_at(&mut self, idx: usize, val: DeltaRational) {
        self.assignment[idx] = val;
    }
    /// Maximum pivot count configured for this instance.
    #[inline]
    pub(super) fn max_pivots(&self) -> usize {
        self.max_pivots
    }
}
pub use super::simplex_opt::SimplexOptStatus;

#[cfg(test)]
mod tests;
