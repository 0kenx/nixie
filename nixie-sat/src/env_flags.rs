//! Process-start-cached instrumentation env probes for hot-path gating.
//!
//! The debug probes (`NIXIE_*_TRACE`, …) are `#[cfg(feature = "std")]`
//! eprintln's gated on an env check.  When that check is a raw
//! `std::env::var` at a per-propagation / per-decision / per-bump call
//! site, the *unarmed* common case pays a full `getenv` walk every time:
//! measured 2026-09-15 on `s38584.cnf` (16 s solve), the round-13 probe
//! set issued **~108 M `getenv` calls** (`NIXIE_CSR_MUT_TRACE` 66 M,
//! `NIXIE_HEAD_TRACE` 30 M, `NIXIE_PICK_TRACE` 7.4 M, …) — ~2/3 of the
//! whole run's cycles (perf: `getenv` 50%, `strncmp` 14%), a ~3× geomean
//! solving-cost regression on the SATCOMP 2025 30-instance sample.
//!
//! Every accessor here reads its env var exactly once per process (the
//! documented intent of `mut_trace`: "the env is read once into a
//! `OnceLock`").  No test toggles these variables mid-process (verified:
//! no test references them), so caching cannot change observable
//! behaviour beyond the cost.

#![cfg(feature = "std")]
#![cfg_attr(not(test), allow(unused))]

use std::sync::OnceLock;

macro_rules! env_flag_fn {
    ($(#[$meta:meta])* $name:ident, $env:expr) => {
        $(#[$meta])*
        pub(crate) fn $name() -> bool {
            static FLAG: OnceLock<bool> = OnceLock::new();
            *FLAG.get_or_init(|| std::env::var($env).is_ok())
        }
    };
}

env_flag_fn!(
    /// `NIXIE_PICK_TRACE` — decision-variable picks (decide/vmtf/search).
    pick_trace,
    "NIXIE_PICK_TRACE"
);
env_flag_fn!(
    /// `NIXIE_HEAD_TRACE` — propagation-queue dequeue per literal.
    head_trace,
    "NIXIE_HEAD_TRACE"
);
env_flag_fn!(
    /// `NIXIE_ENQ_TRACE` — propagation-queue enqueue per literal.
    enq_trace,
    "NIXIE_ENQ_TRACE"
);
env_flag_fn!(
    /// `NIXIE_BUMP_TRACE` — VMTF bump per bump.
    bump_trace,
    "NIXIE_BUMP_TRACE"
);
env_flag_fn!(
    /// `NIXIE_BT_TRACE` — backtracks.
    bt_trace,
    "NIXIE_BT_TRACE"
);
env_flag_fn!(
    /// `NIXIE_AWALK_TRACE` — conflict-analysis walks (per conflict and
    /// per minimization candidate).
    awalk_trace,
    "NIXIE_AWALK_TRACE"
);
env_flag_fn!(
    /// `NIXIE_CONFLICT_TRACE` — BCP-kernel conflict events (per conflict;
    /// the env walk dominated long runs before caching — see module doc).
    conflict_trace,
    "NIXIE_CONFLICT_TRACE"
);
env_flag_fn!(
    /// `NIXIE_CHECK_FIXPOINT` — assignment-fixpoint re-check.
    #[cfg(debug_assertions)]
    check_fixpoint,
    "NIXIE_CHECK_FIXPOINT"
);

/// `NIXIE_DB_DIGEST=<step>` — periodic clause-DB digest (numeric value).
pub(crate) fn db_digest_step() -> Option<u64> {
    static FLAG: OnceLock<Option<u64>> = OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("NIXIE_DB_DIGEST")
            .ok()
            .and_then(|v| v.parse::<u64>().ok())
    })
}

/// `NIXIE_CWRITE=<var>` — clause-write watch trace for one variable.
pub(crate) fn cwrite_target() -> Option<u32> {
    static FLAG: OnceLock<Option<u32>> = OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("NIXIE_CWRITE")
            .ok()
            .and_then(|v| v.parse::<u32>().ok())
    })
}
