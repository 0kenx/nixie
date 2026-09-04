//! Cooperative cancellation tokens for Nixie WASM solves.
//!
//! # Two backing modes
//!
//! - **Local** (default, [`CancellationToken::new`]): a plain in-realm
//!   flag (`Rc<Cell<bool>>`). Only code holding a clone of *this exact*
//!   `CancellationToken` value can observe or flip it -- there is no way
//!   for another thread (e.g. a real `Worker`) to see it, since it never
//!   leaves the JS realm it was created in. This is what
//!   [`crate::js_api::promise_wrapper::AsyncSolver`]'s own `cancel()` uses
//!   today (kept as a `RefCell<bool>` there for API stability) and what
//!   [`crate::js_api::worker_support::WorkerHandler`] uses by default.
//! - **Shared** ([`CancellationToken::new_shared`]): backed by a
//!   [`js_sys::SharedArrayBuffer`], read/written via `Atomics.load` /
//!   `Atomics.store`. When the *same* buffer is handed to a real `Worker`
//!   (see [`crate::js_api::preemptible_worker::PreemptibleSolver`] and
//!   [`crate::js_api::worker_glue`]), a write from the main thread is a
//!   genuine cross-OS-thread signal delivered by the browser engine -- it
//!   does **not** require the worker's JS event loop to be idle, unlike a
//!   `postMessage` "cancel" command (which only gets processed once the
//!   worker's current synchronous JS turn -- which may include a whole
//!   blocking `check_sat()` call -- finishes). This works even though
//!   `nixie-wasm` is built as an ordinary single-threaded WASM module
//!   (no `atomics`/`bulk-memory` target features): `Atomics.load`/`.store`
//!   on a JS-level `SharedArrayBuffer` are plain JS calls performed by the
//!   host engine, independent of whether the WASM module itself has
//!   shared linear memory.
//!
//! # What this can and cannot preempt (read before relying on it)
//!
//! Both modes are **cooperative**: the running WASM code must itself call
//! [`CancellationToken::is_cancelled`] at a call point to notice the flag.
//! Neither mode can interrupt execution at an arbitrary instruction inside
//! a single long-running native call such as `nixie_solver::Context::
//! check_sat` -- that solve loop has no cancellation hook, and adding one
//! is out of scope for `nixie-wasm` (which only depends on `nixie-solver`,
//! it cannot modify it). `nixie-wasm` therefore only polls the flag
//! *between* discrete operations it directly controls (e.g. between
//! successive assertions in a batch, or immediately before starting a
//! `check_sat` call) -- see
//! `crate::js_api::worker_support::WorkerHandler::handle_solve`. That
//! bounds, but does not eliminate, how long a
//! cancelled operation keeps running once a single `check_sat` is
//! in flight.
//!
//! For a HARD guarantee that a stuck solve stops promptly regardless of
//! where it is in its call stack, use
//! [`crate::js_api::preemptible_worker::PreemptibleSolver`], which
//! terminates the underlying `Worker` OS thread outright via
//! `Worker.terminate()`.

#![forbid(unsafe_code)]

use std::cell::Cell;
use std::rc::Rc;
use wasm_bindgen::JsCast;
use wasm_bindgen::prelude::*;

/// Element index (in `i32` units) of the flag within the shared buffer.
const FLAG_INDEX: u32 = 0;
/// Byte length of the [`js_sys::SharedArrayBuffer`] backing a shared
/// token (a single `i32` slot is all that is needed).
const SHARED_BUFFER_BYTES: u32 = 4;
/// Value written into the shared flag slot to mean "cancelled".
const CANCELLED: i32 = 1;
/// Value written into the shared flag slot to mean "not cancelled".
const NOT_CANCELLED: i32 = 0;

enum Backing {
    /// Same-realm flag; see module docs.
    Local(Rc<Cell<bool>>),
    /// `SharedArrayBuffer`-backed flag; see module docs.
    Shared(js_sys::Int32Array),
}

/// A cooperative cancellation flag. See the module documentation for the
/// precise semantics of what this can (and cannot) preempt.
#[wasm_bindgen]
pub struct CancellationToken {
    backing: Backing,
}

#[wasm_bindgen]
impl CancellationToken {
    /// Create a new local (same-realm) cancellation token, not cancelled.
    #[wasm_bindgen(constructor)]
    pub fn new() -> CancellationToken {
        CancellationToken {
            backing: Backing::Local(Rc::new(Cell::new(false))),
        }
    }

    /// Whether the current JS global exposes a working `SharedArrayBuffer`
    /// constructor. Browsers only expose this in a cross-origin-isolated
    /// context (the page must be served with
    /// `Cross-Origin-Opener-Policy: same-origin` and
    /// `Cross-Origin-Embedder-Policy: require-corp`). When this is
    /// `false`, [`CancellationToken::new_shared`] will return an `Err`.
    #[wasm_bindgen(js_name = sharedArrayBufferSupported)]
    pub fn shared_array_buffer_supported() -> bool {
        let global = js_sys::global();
        js_sys::Reflect::get(&global, &JsValue::from_str("SharedArrayBuffer"))
            .map(|v| v.is_function())
            .unwrap_or(false)
    }

    /// Create a new cancellation token backed by a fresh
    /// [`js_sys::SharedArrayBuffer`], not cancelled. Fails with a
    /// descriptive error if `SharedArrayBuffer` is unavailable (see
    /// [`CancellationToken::shared_array_buffer_supported`]) -- callers
    /// should fall back to [`CancellationToken::new`] (local mode) in
    /// that case.
    #[wasm_bindgen(js_name = newShared)]
    pub fn new_shared() -> Result<CancellationToken, JsValue> {
        if !Self::shared_array_buffer_supported() {
            return Err(JsValue::from_str(
                "SharedArrayBuffer is unavailable: the page must be served \
                 cross-origin-isolated (COOP: same-origin, COEP: require-corp) \
                 for shared cooperative cancellation across a real Worker; \
                 fall back to `CancellationToken.new()` (local mode) or use \
                 `PreemptibleSolver`'s hard timeout instead",
            ));
        }
        let buffer = js_sys::SharedArrayBuffer::new(SHARED_BUFFER_BYTES);
        let view = js_sys::Int32Array::new(&buffer);
        js_sys::Atomics::store(&view, FLAG_INDEX, NOT_CANCELLED)?;
        Ok(CancellationToken {
            backing: Backing::Shared(view),
        })
    }

    /// Attach to an existing shared buffer -- e.g. one received from the
    /// main thread in a Worker's `init` message (see
    /// [`crate::js_api::worker_glue`]) via [`CancellationToken::buffer`].
    #[wasm_bindgen(js_name = fromBuffer)]
    pub fn from_buffer(buffer: js_sys::SharedArrayBuffer) -> CancellationToken {
        CancellationToken {
            backing: Backing::Shared(js_sys::Int32Array::new(&buffer)),
        }
    }

    /// The backing [`js_sys::SharedArrayBuffer`], or `None` if this token
    /// is in local mode. Transfer this to a `Worker` via `postMessage`
    /// (no `transfer` list entry needed -- `SharedArrayBuffer` is shared
    /// by reference automatically, unlike a plain `ArrayBuffer`) so both
    /// sides observe the same flag.
    pub fn buffer(&self) -> Option<js_sys::SharedArrayBuffer> {
        match &self.backing {
            Backing::Shared(view) => Some(view.buffer().unchecked_into()),
            Backing::Local(_) => None,
        }
    }

    /// Whether this is a shared (cross-thread-capable) token.
    #[wasm_bindgen(js_name = isShared)]
    pub fn is_shared(&self) -> bool {
        matches!(self.backing, Backing::Shared(_))
    }

    /// Check whether cancellation has been requested. Cheap; safe to call
    /// frequently at solve-loop call points.
    #[wasm_bindgen(js_name = isCancelled)]
    pub fn is_cancelled(&self) -> bool {
        match &self.backing {
            Backing::Local(flag) => flag.get(),
            Backing::Shared(view) => js_sys::Atomics::load(view, FLAG_INDEX)
                .map(|v| v != NOT_CANCELLED)
                .unwrap_or(false),
        }
    }

    /// Request cancellation.
    pub fn cancel(&self) {
        match &self.backing {
            Backing::Local(flag) => flag.set(true),
            Backing::Shared(view) => {
                let _ = js_sys::Atomics::store(view, FLAG_INDEX, CANCELLED);
            }
        }
    }

    /// Clear a pending cancellation so the token can be reused for a
    /// subsequent operation.
    pub fn reset(&self) {
        match &self.backing {
            Backing::Local(flag) => flag.set(false),
            Backing::Shared(view) => {
                let _ = js_sys::Atomics::store(view, FLAG_INDEX, NOT_CANCELLED);
            }
        }
    }
}

impl Default for CancellationToken {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for CancellationToken {
    fn clone(&self) -> Self {
        let backing = match &self.backing {
            Backing::Local(flag) => Backing::Local(flag.clone()),
            Backing::Shared(view) => Backing::Shared(view.clone()),
        };
        CancellationToken { backing }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ======== Local mode: pure Rust (`Rc<Cell<bool>>`), no JS host required ========

    #[test]
    fn test_local_token_default_not_cancelled() {
        let token = CancellationToken::new();
        assert!(!token.is_cancelled());
    }

    #[test]
    fn test_local_token_cancel_and_reset() {
        let token = CancellationToken::new();
        token.cancel();
        assert!(token.is_cancelled());
        token.reset();
        assert!(!token.is_cancelled());
    }

    #[test]
    fn test_local_token_clone_shares_state() {
        // A clone must observe cancellation requested via the original --
        // this is the same-thread "handle to shared flag" contract that
        // `WorkerHandler` and `PreemptibleSolver` rely on internally.
        let token = CancellationToken::new();
        let clone = token.clone();
        assert!(!clone.is_cancelled());
        token.cancel();
        assert!(clone.is_cancelled());
    }

    #[test]
    fn test_local_token_is_not_shared() {
        let token = CancellationToken::new();
        assert!(!token.is_shared());
        assert!(token.buffer().is_none());
    }

    #[test]
    fn test_default_impl_matches_new() {
        let token = CancellationToken::default();
        assert!(!token.is_cancelled());
        assert!(!token.is_shared());
    }

    // -- Shared mode: touches `js_sys::SharedArrayBuffer`/`Atomics`, which
    // panic outside a wasm32 + JS host runtime (verified empirically: see
    // `async_utils` test comments). Gated exactly like the existing
    // `WorkerPool` tests in `js_api::worker_support`.

    #[test]
    #[cfg(target_arch = "wasm32")]
    fn test_shared_array_buffer_supported_does_not_panic() {
        // Availability depends on the JS host's cross-origin-isolation
        // state; only "does not panic" is asserted here.
        let _ = CancellationToken::shared_array_buffer_supported();
    }

    #[test]
    #[cfg(target_arch = "wasm32")]
    fn test_shared_token_round_trips_when_supported() {
        if !CancellationToken::shared_array_buffer_supported() {
            return;
        }
        let token = match CancellationToken::new_shared() {
            Ok(t) => t,
            Err(_) => return,
        };
        assert!(token.is_shared());
        assert!(!token.is_cancelled());

        let buffer = token.buffer().expect("shared token must expose a buffer");
        let attached = CancellationToken::from_buffer(buffer);
        assert!(!attached.is_cancelled());

        token.cancel();
        assert!(
            attached.is_cancelled(),
            "a write through one handle to the SharedArrayBuffer must be \
             visible through another handle attached to the same buffer"
        );

        attached.reset();
        assert!(!token.is_cancelled());
    }
}
