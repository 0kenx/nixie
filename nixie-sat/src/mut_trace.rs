//! Per-literal watch mutation trace (`NIXIE_CSR_MUT_TRACE=<code>`).
//!
//! The commit-B root-cause instrument (CSR study, fifth attempt): logs
//! every mutation of one literal's watch list — Vec side, CSR side, and
//! the dedup-reader asymmetry — with a global operation counter so two
//! runs (or two representations in one run) diff by op order.
//!
//! Zero default cost: the env is read once into a `OnceLock`; every probe
//! is one relaxed load plus a code comparison, and no log line exists
//! unless the trace is armed.

use core::sync::atomic::{AtomicU64, Ordering};

#[cfg(feature = "std")]
use std::sync::OnceLock;

/// The traced literal code, when the env is armed.
#[cfg(feature = "std")]
fn traced_code() -> Option<usize> {
    static CODE: OnceLock<Option<usize>> = OnceLock::new();
    *CODE.get_or_init(|| {
        std::env::var("NIXIE_CSR_MUT_TRACE")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
    })
}

#[cfg(not(feature = "std"))]
fn traced_code() -> Option<usize> {
    None
}

/// Whether any literal is traced (cheap pre-check for call sites that
/// must compute arguments only when logging).
#[allow(dead_code)]
pub(crate) fn armed() -> bool {
    traced_code().is_some() || std::env::var("NIXIE_CSR_MUT_TRACE").as_deref() == Ok("all")
}

/// The global mutation-op counter (strictly increasing per logged event;
/// unlogged mutations do not consume numbers — the counter orders the
/// log, it does not count total work).
pub(crate) fn next_op() -> u64 {
    static OP: AtomicU64 = AtomicU64::new(0);
    OP.fetch_add(1, Ordering::Relaxed)
}

/// Log one mutation event for `code` when it is the traced literal.
///
/// Usage: `mut_trace!(code, "side=vec act=push ref={} blk={}", r, b)`.
#[macro_export]
macro_rules! mut_trace {
    ($code:expr, $($arg:tt)+) => {
        #[cfg(feature = "std")]
        if $crate::mut_trace::armed() && $crate::mut_trace::code_matches($code) {
            eprintln!("[mut op={} code={}] {}", $crate::mut_trace::next_op(), $code, format_args!($($arg)+));
        }
    };
}

/// Whether `code` is the traced literal (the macro's double check keeps
/// `armed()` inlineable and the match behind it).
pub(crate) fn code_matches(code: usize) -> bool {
    match traced_code() {
        Some(c) => c == code,
        // "all" mode: trace every literal (the global stream diff).
        None => std::env::var("NIXIE_CSR_MUT_TRACE").as_deref() == Ok("all"),
    }
}
