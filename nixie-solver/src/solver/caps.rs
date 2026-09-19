//! Completeness caps: observable and overridable for measurement runs.
//!
//! The eager set/bag reductions bound their identity products with caps
//! (`MAX_BAG_ELEMENTS`, `MAX_COUNT_ELEMENTS`, …). A cap firing is a
//! **completeness** event, not a heuristic one: the affected construct is
//! skipped and the honesty gate degrades a `Sat` to `Unknown`, while every
//! `Unsat` stays sound. Two measurement facilities live here so a corpus run
//! can answer "how much completeness would a higher cap buy, and at what
//! cost" without a rebuild:
//!
//! * `NIXIE_DEBUG_CAPS=1` — every firing prints one `[cap] <name>
//!   actual=<n> cap=<limit>` line, greppable from any harness (the TLA+ BMC
//!   survey, the differential fuzzers, the parity suite).
//! * `NIXIE_CAPS=name=value,…` — overrides the defaults for an A/B run.
//!   Unknown names are ignored (measured runs must not silently retune a
//!   cap that no longer exists).
//!
//! The defaults stay in the callers: this module is instrumentation, not
//! policy.

use std::collections::HashMap;
use std::sync::OnceLock;

/// The parsed `NIXIE_CAPS` overrides, read once.
fn overrides() -> &'static HashMap<String, usize> {
    static CACHE: OnceLock<HashMap<String, usize>> = OnceLock::new();
    CACHE.get_or_init(|| {
        let mut out = HashMap::new();
        if let Ok(raw) = std::env::var("NIXIE_CAPS") {
            for pair in raw.split(',') {
                let Some((name, value)) = pair.split_once('=') else {
                    continue;
                };
                if let Ok(v) = value.trim().parse::<usize>() {
                    out.insert(name.trim().to_string(), v);
                }
            }
        }
        out
    })
}

/// The effective limit for `name`, the caller's `default` unless
/// `NIXIE_CAPS` overrides it.
#[must_use]
pub(crate) fn cap(name: &str, default: usize) -> usize {
    overrides().get(name).copied().unwrap_or(default)
}

/// Record that `name` fired at `actual` (already known to exceed `limit`).
/// One line per firing under `NIXIE_DEBUG_CAPS`, so corpus runs tally
/// completeness loss without touching the verdicts.
pub(crate) fn report_fired(name: &str, actual: usize, limit: usize) {
    if std::env::var_os("NIXIE_DEBUG_CAPS").is_some() {
        eprintln!("[cap] {name} actual={actual} cap={limit}");
    }
}
