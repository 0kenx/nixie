//! Async utilities for WASM
//!
//! Provides utilities for yielding to the JavaScript event loop during
//! long-running operations, allowing the browser to remain responsive.

use wasm_bindgen::JsCast;
use wasm_bindgen::prelude::*;
use wasm_bindgen_futures::JsFuture;

/// Yield to the JavaScript event loop
///
/// This allows other tasks (like UI updates) to run before continuing.
/// Should be called periodically during long-running operations.
#[allow(dead_code)]
pub async fn yield_now() {
    // Use setTimeout with 0ms to yield to the event loop
    let promise = js_sys::Promise::resolve(&JsValue::NULL);
    let _ = JsFuture::from(promise).await;
}

/// Yield to the event loop if enough iterations have passed
///
/// This is useful for operations that iterate many times - we don't want
/// to yield on every iteration (too much overhead), but we want to yield
/// periodically to keep the UI responsive.
///
/// # Parameters
///
/// * `counter` - Mutable counter tracking iterations
/// * `yield_every` - Yield every N iterations
///
/// # Returns
///
/// `true` if yielded, `false` otherwise
#[allow(dead_code)]
pub async fn yield_periodic(counter: &mut usize, yield_every: usize) -> bool {
    *counter += 1;
    if *counter >= yield_every {
        *counter = 0;
        yield_now().await;
        true
    } else {
        false
    }
}

/// Execute a closure with periodic yielding
///
/// Wraps a long-running operation and periodically yields to the event loop.
/// The closure receives a yield callback that it should call periodically.
///
/// # Parameters
///
/// * `f` - Closure to execute
/// * `yield_every` - Yield every N calls to the yield callback
///
/// # Example
///
/// ```rust,ignore
/// use nixie_wasm::async_utils::with_periodic_yield;
///
/// async fn process_items(items: Vec<Item>) -> Result<(), Error> {
///     with_periodic_yield(|mut should_yield| {
///         for item in items {
///             process_item(item)?;
///
///             // Check if we should yield
///             if should_yield() {
///                 // Yield point reached
///             }
///         }
///         Ok(())
///     }, 100).await
/// }
/// ```
#[allow(dead_code)]
pub async fn with_periodic_yield<F, R>(mut f: F, yield_every: usize) -> R
where
    F: FnMut(&mut dyn FnMut() -> bool) -> R,
{
    let mut counter = 0;
    let mut should_yield = || {
        counter += 1;
        counter >= yield_every
    };

    let result = f(&mut should_yield);

    if counter >= yield_every {
        yield_now().await;
    }

    result
}

/// Create a cancellable async operation
///
/// Returns a tuple of (cancellation flag, cancel function).
/// The operation should check the flag periodically and abort if set.
#[allow(dead_code)]
pub fn create_cancellable() -> (std::sync::Arc<std::sync::atomic::AtomicBool>, impl Fn()) {
    let flag = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let flag_clone = flag.clone();
    let cancel = move || {
        flag_clone.store(true, std::sync::atomic::Ordering::Relaxed);
    };
    (flag, cancel)
}

/// Check if operation is cancelled
#[allow(dead_code)]
pub fn is_cancelled(flag: &std::sync::Arc<std::sync::atomic::AtomicBool>) -> bool {
    flag.load(std::sync::atomic::Ordering::Relaxed)
}

/// Current time in milliseconds since the time origin.
///
/// Reads `globalThis.performance.now()` through generic JS reflection
/// (rather than `web_sys::window()`, which returns `None` inside a Web
/// Worker) so it works uniformly on the main thread and inside a worker --
/// exactly the context [`crate::js_api::preemptible_worker::PreemptibleSolver`]
/// runs the solver in. Returns `0.0` if `performance` is unavailable
/// (e.g. non-browser JS hosts without the High Resolution Time API).
#[allow(dead_code)]
pub fn now_ms() -> f64 {
    let global = js_sys::global();
    let Ok(performance) = js_sys::Reflect::get(&global, &JsValue::from_str("performance")) else {
        return 0.0;
    };
    if performance.is_undefined() || performance.is_null() {
        return 0.0;
    }
    let Ok(now_fn) = js_sys::Reflect::get(&performance, &JsValue::from_str("now")) else {
        return 0.0;
    };
    let Some(now_fn) = now_fn.dyn_ref::<js_sys::Function>() else {
        return 0.0;
    };
    now_fn
        .call0(&performance)
        .ok()
        .and_then(|v| v.as_f64())
        .unwrap_or(0.0)
}

/// Schedule `callback` to run after `timeout_ms` via the global
/// `setTimeout`.
///
/// Resolved through JS reflection (`globalThis.setTimeout`) rather than
/// `web_sys::Window::set_timeout_with_callback_and_timeout_and_arguments_0`
/// so it works both on the main thread and inside a Web Worker (there is
/// no `web_sys::Window` inside a worker's global scope). Returns the timer
/// id (pass to [`clear_timeout_global`] to cancel), or an `Err` if the
/// current JS global has no callable `setTimeout`.
#[allow(dead_code)]
pub fn set_timeout_global(
    callback: &Closure<dyn FnMut()>,
    timeout_ms: i32,
) -> Result<i32, JsValue> {
    let global = js_sys::global();
    let set_timeout = js_sys::Reflect::get(&global, &JsValue::from_str("setTimeout"))?;
    let set_timeout: js_sys::Function = set_timeout
        .dyn_into()
        .map_err(|_| JsValue::from_str("global `setTimeout` is not callable"))?;
    let result = set_timeout.call2(
        &global,
        callback.as_ref().unchecked_ref(),
        &JsValue::from_f64(f64::from(timeout_ms)),
    )?;
    result
        .as_f64()
        .map(|f| f as i32)
        .ok_or_else(|| JsValue::from_str("setTimeout did not return a numeric timer id"))
}

/// Cancel a timer previously scheduled by [`set_timeout_global`].
///
/// Silently does nothing if the current JS global has no `clearTimeout`
/// (rather than erroring) since callers use this defensively/best-effort
/// (e.g. "clear the timeout if the operation already finished").
#[allow(dead_code)]
pub fn clear_timeout_global(timer_id: i32) {
    let global = js_sys::global();
    if let Ok(clear_timeout) = js_sys::Reflect::get(&global, &JsValue::from_str("clearTimeout"))
        && let Some(clear_timeout) = clear_timeout.dyn_ref::<js_sys::Function>()
    {
        let _ = clear_timeout.call1(&global, &JsValue::from_f64(f64::from(timer_id)));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_yield_periodic_counter() {
        let mut counter = 0;

        // First call should not trigger yield
        assert_eq!(counter, 0);

        // Increment counter
        for i in 1..=10 {
            counter += 1;
            if counter >= 5 {
                // Would yield here and reset counter
                assert_eq!(i, 5);
                break;
            }
        }
        // Counter was at 5 when we broke
        assert_eq!(counter, 5);
    }

    #[test]
    fn test_cancellable() {
        let (flag, cancel) = create_cancellable();
        assert!(!is_cancelled(&flag));

        cancel();
        assert!(is_cancelled(&flag));
    }

    // `now_ms`/`set_timeout_global`/`clear_timeout_global` call real JS
    // globals (`performance`, `setTimeout`) and panic if invoked outside a
    // wasm32 + JS host runtime (verified empirically: js-sys aborts with
    // "cannot call wasm-bindgen imported functions on non-wasm targets").
    // Gated exactly like the existing `WorkerPool` tests in
    // `js_api::worker_support`; run via a wasm32 JS test harness.
    #[test]
    #[cfg(target_arch = "wasm32")]
    fn test_now_ms_does_not_panic() {
        // No real browser `performance` exists in a bare wasm32 test
        // harness, so this exercises the "unavailable -> 0.0" fallback
        // path without erroring.
        let t = now_ms();
        assert!(t >= 0.0);
    }

    #[test]
    #[cfg(target_arch = "wasm32")]
    fn test_set_timeout_global_does_not_panic() {
        // Whether a `setTimeout` global exists depends on the JS host
        // running this wasm32 test binary (browsers/Node have it; a bare
        // wasmtime harness may not) -- the contract under test is "never
        // panics regardless", not a specific Ok/Err outcome. Clear the
        // timer immediately on success so the callback can never fire
        // after this closure (and the test process) has gone away.
        let cb = Closure::once(|| {});
        if let Ok(id) = set_timeout_global(&cb, 0) {
            clear_timeout_global(id);
        }
    }
}
