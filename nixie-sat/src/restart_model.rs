//! Faithful port of cadical's restart machinery: unbiased EMAs, Knuth's
//! "reluctant doubling" (Luby) for stable-mode restarts, and per-mode
//! glue averages that swap on stable/focused transitions.
//!
//! See cadical's `ema.cpp`, `reluctant.hpp`, `averages.{hpp,cpp}` and
//! `restart.cpp`. The complexity is load-bearing: the very slow glue EMA
//! (window 1e5) makes the Glucose restart condition meaningful, the
//! reluctant sequence gives stable mode its quiet Luby phases, and the
//! per-mode averaged EMAs let each mode track clause quality independently.

/// Unbiased exponential moving average (ADAM-style bias correction), ported
/// from cadical's `EMA`. `alpha = 1/window`.
#[derive(Clone, Copy, Default, Debug)]
pub struct Ema {
    value: f64,  // unbiased (corrected) moving average
    biased: f64, // biased initialized moving average
    alpha: f64,  // input scaling
    beta: f64,   // decay of biased (1 - alpha)
    exp: f64,    // beta^updated
}

impl Ema {
    /// New EMA with the given window size (`alpha = 1/window`).
    #[must_use]
    pub fn new(window: f64) -> Self {
        let alpha = 1.0 / window.max(1.0);
        let beta = 1.0 - alpha;
        Self {
            value: 0.0,
            biased: 0.0,
            alpha,
            beta,
            exp: if beta != 0.0 { 1.0 } else { 0.0 },
        }
    }

    /// Feed a new sample.
    pub fn update(&mut self, y: f64) {
        self.biased += self.alpha * (y - self.biased);
        if self.exp != 0.0 {
            self.exp *= self.beta;
            // Guard against the divisor collapsing to ~0 via FP underflow.
            let div = 1.0 - self.exp;
            self.value = if div > 1e-12 {
                self.biased / div
            } else {
                self.biased
            };
        } else {
            self.value = self.biased;
        }
    }

    #[must_use]
    pub fn value(&self) -> f64 {
        self.value
    }
}

/// Per-mode glue averages (fast/slow EMAs), swapped between current/saved on
/// each stable/focused transition (`swap_averages`).
#[derive(Clone, Copy, Debug)]
pub struct GlueAverages {
    pub fast: Ema,
    pub slow: Ema,
}

impl GlueAverages {
    /// cadical defaults: `emagluefast = 33`, `emaglueslow = 1e5`.
    #[must_use]
    pub fn new() -> Self {
        Self {
            fast: Ema::new(33.0),
            slow: Ema::new(1e5),
        }
    }
}

impl Default for GlueAverages {
    fn default() -> Self {
        Self::new()
    }
}

/// Knuth's "reluctant doubling" (the Luby restart sequence), ported from
/// cadical's `Reluctant`. Used for stable-mode restarts: ticks every conflict,
/// fires (`activated`) after `v * period` conflicts, where `v` follows the
/// Luby sequence. `limit` caps the maximum doubling period.
#[derive(Clone, Copy, Default, Debug)]
pub struct Reluctant {
    u: u64,
    v: u64,
    limit: u64,
    period: u64,
    countdown: u64,
    trigger: bool,
    limited: bool,
}

impl Reluctant {
    /// Enable with base `period` (cadical `reluctantint = 1024`) and optional
    /// `limit` (cadical `reluctantmax = 1<<20`); `limit == 0` means unbounded.
    pub fn enable(&mut self, period: u64, limit: u64) {
        self.u = 1;
        self.v = 1;
        self.period = period;
        self.countdown = period;
        self.trigger = false;
        self.limited = limit > 0;
        self.limit = limit;
    }

    pub fn disable(&mut self) {
        self.period = 0;
        self.trigger = false;
    }

    /// Advance one conflict. Sets the trigger when the current Luby period
    /// elapses.
    pub fn tick(&mut self) {
        if self.period == 0 || self.trigger {
            return;
        }
        if self.countdown > 1 {
            self.countdown -= 1;
            return;
        }
        // countdown hit zero – advance the Luby doubling (DK formulation).
        if (self.u & self.u.wrapping_neg()) == self.v {
            self.u += 1;
            self.v = 1;
        } else {
            self.v *= 2;
        }
        if self.limited && self.v >= self.limit {
            self.u = 1;
            self.v = 1;
        }
        self.countdown = self.v.saturating_mul(self.period);
        self.trigger = true;
    }

    /// Consume the trigger (returns true once per Luby period).
    pub fn activated(&mut self) -> bool {
        if !self.trigger {
            return false;
        }
        self.trigger = false;
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ema_converges_and_is_unbiased() {
        let mut e = Ema::new(4.0); // alpha 0.25
        for _ in 0..1000 {
            e.update(10.0);
        }
        assert!((e.value() - 10.0).abs() < 1e-6, "EMA should converge to 10");
    }

    #[test]
    fn reluctant_is_disabled_by_default() {
        let mut r = Reluctant::default();
        for _ in 0..100 {
            r.tick();
        }
        assert!(!r.activated());
    }

    #[test]
    fn reluctant_fires_after_period() {
        let mut r = Reluctant::default();
        r.enable(4, 0);
        // first Luby value v=1, period 4 → fires after 4 ticks.
        for _ in 0..3 {
            r.tick();
            assert!(!r.activated());
        }
        r.tick();
        assert!(r.activated());
    }
}
