//! Restart timing primitives for the stable/focused search schedule.
//!
//! Two independent building blocks used by [`crate::solver::Solver`] to decide
//! *when* to restart:
//!
//! - [`BiasCorrectedEma`]: an exponential moving average with startup bias
//!   correction, so early samples are not underweighted by the usual
//!   `value = value + alpha*(sample-value)` recurrence. Two of these (a short
//!   and a long window) track recent vs. long-run clause quality (LBD); the
//!   short one running ahead of the long one is the signal that search has
//!   drifted into low-quality territory and a restart is due (the Glucose
//!   restart condition).
//! - [`LubyClock`]: a streaming generator of Knuth's "reluctant doubling"
//!   sequence (which reproduces the Luby sequence without recomputing it from
//!   scratch every restart). Used to schedule restarts during the search's
//!   *stable* phase, where the quiet, slowly-growing Luby rhythm avoids the
//!   thrashing that a fixed short interval would cause.
//!
//! Background: G. Biere's CaDiCaL solver popularized alternating short
//! "focused" search bursts (frequent Glucose-EMA restarts) with long
//! "stable" bursts (rare Luby restarts) as a way to get the benefits of both
//! restart philosophies without committing to either one for a whole run.
//! This module provides the two timers that schedule alternates; the mode
//! switch itself lives in `Solver::check_stabilize`.

/// Bias-corrected exponential moving average.
///
/// A plain EMA started at 0 underestimates its true average for the first
/// `~window` samples, because the initial 0 is itself weighted into the
/// recurrence. This divides out that startup bias (the classic "Adam-style"
/// correction: divide the raw EMA by `1 - beta^n` after `n` updates), so the
/// reported value is a fair average from the very first sample.
#[derive(Debug, Clone, Copy)]
pub struct BiasCorrectedEma {
    /// Smoothing factor applied to each new sample (`1 / window`).
    alpha: f64,
    /// `1 - alpha`, the weight retained from the previous average.
    retain: f64,
    /// Raw (biased) running average.
    raw: f64,
    /// Bias-correction denominator, `retain^n` after `n` updates; starts at 1
    /// and decays toward 0, at which point correction becomes a no-op.
    correction: f64,
    /// Corrected value returned by [`Self::get`].
    corrected: f64,
}

impl BiasCorrectedEma {
    /// Build a tracker with the given averaging window (in samples).
    ///
    /// A window `<= 0` is treated as 1 (no smoothing: each sample replaces
    /// the average outright).
    #[must_use]
    pub fn with_window(window: f64) -> Self {
        let alpha = 1.0 / window.max(1.0);
        Self {
            alpha,
            retain: 1.0 - alpha,
            raw: 0.0,
            correction: 1.0,
            corrected: 0.0,
        }
    }

    /// Feed one new sample into the average.
    pub fn observe(&mut self, sample: f64) {
        self.raw += self.alpha * (sample - self.raw);
        self.correction *= self.retain;
        // Once the correction factor has decayed into the FP noise floor,
        // dividing by it would amplify rounding error for no benefit — the
        // raw average has already converged.
        self.corrected = if self.correction > 1e-12 {
            self.raw / (1.0 - self.correction)
        } else {
            self.raw
        };
    }

    /// Current (bias-corrected) average.
    #[must_use]
    pub fn get(&self) -> f64 {
        self.corrected
    }
}

impl Default for BiasCorrectedEma {
    /// A window of 1 sample (no smoothing). Callers should normally use
    /// [`Self::with_window`] with a domain-appropriate window instead.
    fn default() -> Self {
        Self::with_window(1.0)
    }
}

/// Short/long LBD trackers for one search mode (focused or stable), used to
/// detect quality degradation for the Glucose restart condition.
///
/// Kept as one struct per mode (`Solver` holds a "current" and "saved" pair,
/// swapped on every stable/focused transition) so each mode's restart
/// judgement is based only on samples gathered while that mode was active.
#[derive(Debug, Clone, Copy)]
pub struct ModeLbdTrackers {
    /// Short window: tracks the last few dozen learned clauses' glue.
    pub recent: BiasCorrectedEma,
    /// Long window: tracks the glue trend over the whole mode run.
    pub baseline: BiasCorrectedEma,
}

impl ModeLbdTrackers {
    /// CaDiCaL-derived defaults: a ~33-sample recent window is short enough
    /// to react within a few restarts; a 100,000-sample baseline is long
    /// enough to be a stable reference even on long runs.
    #[must_use]
    pub fn new() -> Self {
        Self {
            recent: BiasCorrectedEma::with_window(33.0),
            baseline: BiasCorrectedEma::with_window(100_000.0),
        }
    }
}

impl Default for ModeLbdTrackers {
    fn default() -> Self {
        Self::new()
    }
}

/// Streaming generator for Knuth's reluctant-doubling sequence (TAOCP
/// 6.2.1(63)): the same restart lengths as the Luby sequence, produced
/// incrementally in O(1) per tick instead of recomputed from an index.
///
/// Ticked once per unit of progress (here: once per conflict); fires
/// (consumed by [`Self::due`]) every time the current Luby term times the
/// base period has elapsed. An optional ceiling re-synchronizes the sequence
/// back to its start once a term would otherwise exceed it, capping how long
/// a single quiet stretch can run.
#[derive(Debug, Clone, Copy, Default)]
pub struct LubyClock {
    outer: u64,
    inner: u64,
    ceiling: u64,
    period: u64,
    remaining: u64,
    due: bool,
    capped: bool,
}

impl LubyClock {
    /// Arm the clock with a base `period` (ticks per Luby unit) and an
    /// optional `ceiling` on the Luby term (0 = unbounded).
    pub fn arm(&mut self, period: u64, ceiling: u64) {
        self.outer = 1;
        self.inner = 1;
        self.period = period;
        self.remaining = period;
        self.due = false;
        self.capped = ceiling > 0;
        self.ceiling = ceiling;
    }

    /// Disarm the clock: [`Self::tick`] becomes a no-op and [`Self::due`]
    /// stays permanently false until the next [`Self::arm`].
    pub fn disarm(&mut self) {
        self.period = 0;
        self.due = false;
    }

    /// Advance the clock by one unit of progress.
    pub fn tick(&mut self) {
        if self.period == 0 || self.due {
            return;
        }
        if self.remaining > 1 {
            self.remaining -= 1;
            return;
        }
        // `remaining` just hit zero: advance to the next Luby term using the
        // standard reluctant-doubling bit trick — if the lowest set bit of
        // `outer` equals `inner`, start a new "octave" (bump `outer`, reset
        // `inner`); otherwise double `inner` within the current octave.
        if (self.outer & self.outer.wrapping_neg()) == self.inner {
            self.outer += 1;
            self.inner = 1;
        } else {
            self.inner *= 2;
        }
        if self.capped && self.inner >= self.ceiling {
            self.outer = 1;
            self.inner = 1;
        }
        self.remaining = self.inner.saturating_mul(self.period);
        self.due = true;
    }

    /// Consume a pending restart signal. Returns `true` at most once per
    /// elapsed Luby term.
    pub fn due(&mut self) -> bool {
        if !self.due {
            return false;
        }
        self.due = false;
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ema_converges_to_constant_input() {
        let mut ema = BiasCorrectedEma::with_window(8.0);
        for _ in 0..500 {
            ema.observe(4.0);
        }
        assert!((ema.get() - 4.0).abs() < 1e-6);
    }

    #[test]
    fn ema_is_not_biased_toward_zero_on_first_sample() {
        // With no bias correction the first sample would report `alpha *
        // sample`, far below `sample` itself. The corrected value should
        // land exactly on the first observation.
        let mut ema = BiasCorrectedEma::with_window(10.0);
        ema.observe(20.0);
        assert!((ema.get() - 20.0).abs() < 1e-9);
    }

    #[test]
    fn luby_clock_idle_until_armed() {
        let mut clock = LubyClock::default();
        for _ in 0..1000 {
            clock.tick();
        }
        assert!(!clock.due());
    }

    #[test]
    fn luby_clock_fires_after_first_period() {
        let mut clock = LubyClock::default();
        clock.arm(5, 0);
        for _ in 0..4 {
            clock.tick();
            assert!(!clock.due());
        }
        clock.tick();
        assert!(clock.due());
        // Consuming `due` clears it until the next elapsed term.
        assert!(!clock.due());
    }

    #[test]
    fn luby_clock_ceiling_resynchronizes() {
        // With a tiny ceiling, the inner term can never grow past it, so the
        // sequence keeps resetting to the base period instead of the terms
        // growing unbounded.
        let mut clock = LubyClock::default();
        clock.arm(2, 4);
        let mut fires = 0;
        for _ in 0..40 {
            clock.tick();
            if clock.due() {
                fires += 1;
            }
        }
        // Bounded period means noticeably more restarts fire than an
        // unbounded sequence would produce in the same number of ticks.
        assert!(fires >= 8, "expected frequent capped restarts, got {fires}");
    }
}
