//! Hard-preemptible solving via a dedicated Web Worker.
//!
//! [`crate::js_api::promise_wrapper::AsyncOperation::execute`]'s
//! `withTimeout` races the solve `Promise` against a `setTimeout`
//! `Promise` -- but `checkSatAsync` runs `Context::check_sat()` to
//! completion inside a single synchronous poll with no interior `.await`,
//! so on a single-threaded JS host the timeout callback cannot even run,
//! let alone preempt anything, until the solve has already returned. That
//! is fundamental: a thread cannot terminate its own synchronous
//! execution from within a callback queued on that same thread.
//!
//! [`PreemptibleSolver`] instead runs the solver inside a dedicated
//! `web_sys::Worker` -- a real OS thread the browser schedules
//! independently of the main thread -- and, on timeout, calls
//! `Worker.terminate()` from the MAIN thread. The browser guarantees this
//! stops the worker's execution immediately, unconditionally, regardless
//! of what it is doing. A fresh worker is spawned right after so the
//! instance stays usable for the next call.

#![forbid(unsafe_code)]

use crate::async_utils;
use crate::js_api::cancellation::CancellationToken;
use crate::js_api::worker_glue::generate_worker_bootstrap_js;
use crate::{WasmError, WasmErrorKind};
use js_sys::Promise;
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;
use wasm_bindgen::JsCast;
use wasm_bindgen::prelude::*;

type OnMessageClosure = Closure<dyn FnMut(web_sys::MessageEvent)>;
type OnErrorClosure = Closure<dyn FnMut(web_sys::ErrorEvent)>;

struct PendingCall {
    resolve: js_sys::Function,
    reject: js_sys::Function,
    /// Timer id from [`async_utils::set_timeout_global`], if this call was
    /// dispatched with a timeout -- cleared once the call settles for any
    /// reason so the timer callback becomes a no-op.
    timer_id: Option<i32>,
}

/// Owns a dedicated `Worker` running the Nixie solver, and can HARD-kill it
/// (`Worker.terminate()`) from the main thread on timeout.
///
/// # Timeout semantics (read before using)
///
/// - [`PreemptibleSolver::solve_with_timeout`]'s timeout is a **hard**
///   timeout: on expiry the underlying `Worker`'s OS thread is terminated
///   via `Worker.terminate()`, which the browser guarantees stops
///   execution immediately, regardless of what the solver is doing
///   (including in the middle of a single `check_sat` call). A fresh
///   `Worker` is spawned right after so this instance remains usable for
///   the next call. This is the guarantee
///   [`crate::js_api::promise_wrapper::AsyncOperation`] cannot provide.
/// - [`PreemptibleSolver::cancellation_buffer`] exposes a SEPARATE,
///   best-effort **cooperative** mechanism (see
///   [`CancellationToken`]'s docs): flipping it lets you *request* the
///   worker stop of its own accord between operations, without losing
///   worker state or paying the cost of a full respawn, but it is never
///   observed in the middle of a single `check_sat` call. Prefer the hard
///   timeout whenever you need an actual guarantee.
#[wasm_bindgen]
pub struct PreemptibleSolver {
    wasm_js_url: String,
    wasm_bg_url: String,
    worker: Rc<RefCell<Option<web_sys::Worker>>>,
    on_message: Rc<RefCell<Option<OnMessageClosure>>>,
    on_error: Rc<RefCell<Option<OnErrorClosure>>>,
    next_id: Rc<Cell<u32>>,
    pending: Rc<RefCell<HashMap<u32, PendingCall>>>,
    cancellation: CancellationToken,
}

#[wasm_bindgen]
impl PreemptibleSolver {
    /// Spawn a new preemptible solver.
    ///
    /// `wasm_js_url`/`wasm_bg_url` are the URLs of the `--target
    /// no-modules` wasm-bindgen glue (`*.js`) and wasm binary
    /// (`*_bg.wasm`) that the generated worker bootstrap will load --
    /// see [`generate_worker_bootstrap_js`].
    #[wasm_bindgen(constructor)]
    pub fn new(wasm_js_url: String, wasm_bg_url: String) -> Result<PreemptibleSolver, JsValue> {
        let cancellation = if CancellationToken::shared_array_buffer_supported() {
            CancellationToken::new_shared().unwrap_or_else(|_| CancellationToken::new())
        } else {
            CancellationToken::new()
        };

        let solver = PreemptibleSolver {
            wasm_js_url,
            wasm_bg_url,
            worker: Rc::new(RefCell::new(None)),
            on_message: Rc::new(RefCell::new(None)),
            on_error: Rc::new(RefCell::new(None)),
            next_id: Rc::new(Cell::new(0)),
            pending: Rc::new(RefCell::new(HashMap::new())),
            cancellation,
        };
        spawn_worker_into(
            &solver.worker,
            &solver.on_message,
            &solver.on_error,
            &solver.pending,
            &solver.wasm_js_url,
            &solver.wasm_bg_url,
        )?;
        Ok(solver)
    }

    /// Run `script` (a full SMT-LIB2 script, e.g. `(set-logic QF_LIA)
    /// (declare-const x Int) (assert (> x 0)) (check-sat)`) on the
    /// worker. If `timeout_ms` elapses before the worker responds, the
    /// worker is HARD-terminated (see type-level docs) and the returned
    /// promise rejects; a fresh worker is spawned automatically so this
    /// instance remains usable afterwards.
    #[wasm_bindgen(js_name = solveWithTimeout)]
    pub fn solve_with_timeout(&self, script: String, timeout_ms: u32) -> Promise {
        self.dispatch(script, Some(timeout_ms))
    }

    /// Run `script` with no timeout -- the returned promise settles only
    /// when the worker responds, errors, or [`PreemptibleSolver::terminate`]
    /// is called.
    pub fn solve(&self, script: String) -> Promise {
        self.dispatch(script, None)
    }

    /// Immediately hard-terminate the current worker (exactly what a
    /// timeout does) and spawn a fresh one. Every pending call is
    /// rejected.
    pub fn terminate(&self) -> Result<(), JsValue> {
        reject_all_pending(&self.pending, "worker terminated manually");
        spawn_worker_into(
            &self.worker,
            &self.on_message,
            &self.on_error,
            &self.pending,
            &self.wasm_js_url,
            &self.wasm_bg_url,
        )
    }

    /// The `SharedArrayBuffer` backing this solver's cooperative
    /// cancellation token, or `None` if the page is not
    /// cross-origin-isolated (see [`CancellationToken`]). Send this to
    /// other code that should be able to *request* cancellation (e.g. via
    /// [`CancellationToken::from_buffer`] + `.cancel()`); it is honored
    /// only at call points inside `nixie-wasm`, never inside a single
    /// `check_sat` call -- prefer [`PreemptibleSolver::solve_with_timeout`]
    /// for a hard guarantee.
    #[wasm_bindgen(js_name = cancellationBuffer)]
    pub fn cancellation_buffer(&self) -> Option<js_sys::SharedArrayBuffer> {
        self.cancellation.buffer()
    }

    /// Request cooperative cancellation via the shared buffer. A no-op
    /// (silently ignored by the worker) when
    /// [`PreemptibleSolver::cancellation_buffer`] is `None`, since in that
    /// case the worker never received a buffer to attach to either.
    #[wasm_bindgen(js_name = requestCooperativeCancel)]
    pub fn request_cooperative_cancel(&self) {
        self.cancellation.cancel();
    }

    /// Whether a `Worker` is currently spawned and ready to receive work.
    #[wasm_bindgen(js_name = isReady)]
    pub fn is_ready(&self) -> bool {
        self.worker.borrow().is_some()
    }

    fn dispatch(&self, script: String, timeout_ms: Option<u32>) -> Promise {
        let id = self.next_id.get();
        self.next_id.set(id.wrapping_add(1));

        let worker = self.worker.borrow().clone();
        let Some(worker) = worker else {
            return Promise::reject(
                &WasmError::new(
                    WasmErrorKind::InvalidState,
                    "worker is not spawned (a previous hard-timeout respawn may have failed; \
                     call terminate() to retry)",
                )
                .into(),
            );
        };

        let msg = js_sys::Object::new();
        let _ = js_sys::Reflect::set(&msg, &"id".into(), &JsValue::from_f64(f64::from(id)));
        let _ = js_sys::Reflect::set(&msg, &"type".into(), &"solve".into());
        let data = js_sys::Object::new();
        let _ = js_sys::Reflect::set(&data, &"script".into(), &script.into());
        if let Some(buffer) = self.cancellation.buffer() {
            let _ = js_sys::Reflect::set(&data, &"cancellationBuffer".into(), &buffer);
        }
        let _ = js_sys::Reflect::set(&msg, &"data".into(), &data);

        let pending = self.pending.clone();
        let worker_slot = self.worker.clone();
        let on_message_slot = self.on_message.clone();
        let on_error_slot = self.on_error.clone();
        let wasm_js_url = self.wasm_js_url.clone();
        let wasm_bg_url = self.wasm_bg_url.clone();

        Promise::new(&mut |resolve, reject| {
            let timer_id = timeout_ms.and_then(|ms| {
                let pending_to = pending.clone();
                let worker_to = worker_slot.clone();
                let on_message_to = on_message_slot.clone();
                let on_error_to = on_error_slot.clone();
                let wasm_js_url_to = wasm_js_url.clone();
                let wasm_bg_url_to = wasm_bg_url.clone();
                let reject_to = reject.clone();

                let timeout_closure = Closure::once(move || {
                    // If the call already settled (a real response beat
                    // the timer), `pending_to` no longer has this id --
                    // nothing to do.
                    if pending_to.borrow_mut().remove(&id).is_none() {
                        return;
                    }

                    if let Some(w) = worker_to.borrow_mut().take() {
                        w.set_onmessage(None);
                        w.set_onerror(None);
                        w.terminate();
                    }
                    on_message_to.borrow_mut().take();
                    on_error_to.borrow_mut().take();

                    let error = WasmError::new(
                        WasmErrorKind::InvalidState,
                        format!(
                            "hard timeout after {ms}ms: worker terminated (this is a real \
                             preemption via Worker.terminate(), not a cooperative check)"
                        ),
                    );
                    let _ = reject_to.call1(&JsValue::NULL, &error.into());

                    if let Err(err) = spawn_worker_into(
                        &worker_to,
                        &on_message_to,
                        &on_error_to,
                        &pending_to,
                        &wasm_js_url_to,
                        &wasm_bg_url_to,
                    ) {
                        web_sys::console::error_2(
                            &"Nixie PreemptibleSolver: failed to respawn worker after hard \
                              timeout; call terminate() to retry:"
                                .into(),
                            &err,
                        );
                    }
                });

                let handle = async_utils::set_timeout_global(&timeout_closure, ms as i32).ok();
                // The closure must outlive this call (it fires later, on
                // the JS event loop); `.forget()` intentionally leaks it
                // -- it self-cleans by removing its own pending entry, and
                // is short-lived (one timer per solve call).
                timeout_closure.forget();
                handle
            });

            pending.borrow_mut().insert(
                id,
                PendingCall {
                    resolve: resolve.clone(),
                    reject: reject.clone(),
                    timer_id,
                },
            );

            if let Err(err) = worker.post_message(&msg)
                && let Some(call) = pending.borrow_mut().remove(&id)
            {
                if let Some(t) = call.timer_id {
                    async_utils::clear_timeout_global(t);
                }
                let _ = call.reject.call1(&JsValue::NULL, &err);
            }
        })
    }
}

impl Drop for PreemptibleSolver {
    fn drop(&mut self) {
        if let Some(w) = self.worker.borrow_mut().take() {
            w.set_onmessage(None);
            w.set_onerror(None);
            w.terminate();
        }
    }
}

/// Reject every currently pending call with `message`, clearing their
/// timers first so a later-firing timeout callback cannot double-settle
/// an already-rejected promise.
fn reject_all_pending(pending: &Rc<RefCell<HashMap<u32, PendingCall>>>, message: &str) {
    for (_, call) in pending.borrow_mut().drain() {
        if let Some(t) = call.timer_id {
            async_utils::clear_timeout_global(t);
        }
        let error = WasmError::new(WasmErrorKind::InvalidState, message.to_string());
        let _ = call.reject.call1(&JsValue::NULL, &error.into());
    }
}

/// Tear down any previous worker/closures (if present) and spawn a fresh
/// one, wiring `onmessage`/`onerror` to settle entries in `pending`.
///
/// Free function (rather than a method) because it must be callable from
/// inside a `'static` timeout closure that does not have access to `&self`.
fn spawn_worker_into(
    worker_slot: &Rc<RefCell<Option<web_sys::Worker>>>,
    on_message_slot: &Rc<RefCell<Option<OnMessageClosure>>>,
    on_error_slot: &Rc<RefCell<Option<OnErrorClosure>>>,
    pending: &Rc<RefCell<HashMap<u32, PendingCall>>>,
    wasm_js_url: &str,
    wasm_bg_url: &str,
) -> Result<(), JsValue> {
    // Tear down any previous worker/closures first: unhook its handlers
    // and terminate it *before* dropping the closures they reference, so
    // a message that arrives on the old worker after this point can never
    // invoke an already-dropped closure.
    if let Some(old) = worker_slot.borrow_mut().take() {
        old.set_onmessage(None);
        old.set_onerror(None);
        old.terminate();
    }
    on_message_slot.borrow_mut().take();
    on_error_slot.borrow_mut().take();

    let bootstrap_js = generate_worker_bootstrap_js(wasm_js_url, wasm_bg_url);
    let parts = js_sys::Array::new();
    parts.push(&JsValue::from_str(&bootstrap_js));
    let bag = web_sys::BlobPropertyBag::new();
    bag.set_type("application/javascript");
    let blob = web_sys::Blob::new_with_str_sequence_and_options(&parts, &bag)?;
    let url = web_sys::Url::create_object_url_with_blob(&blob)?;

    let worker = web_sys::Worker::new(&url)?;
    // The object URL only needs to live long enough for the browser to
    // fetch/parse the worker script; revoking it immediately is good
    // hygiene and does not affect the already-spawned worker.
    let _ = web_sys::Url::revoke_object_url(&url);

    let on_message_pending = pending.clone();
    let on_message_closure: OnMessageClosure =
        Closure::wrap(Box::new(move |event: web_sys::MessageEvent| {
            let data = event.data();
            let id = js_sys::Reflect::get(&data, &"id".into())
                .ok()
                .and_then(|v| v.as_f64())
                .map(|f| f as u32);
            let Some(id) = id else { return };
            let Some(call) = on_message_pending.borrow_mut().remove(&id) else {
                // No matching pending call -- either it already settled
                // via a hard timeout, or this is an unexpected/duplicate
                // message. Either way there is nothing to resolve/reject.
                return;
            };
            if let Some(timer_id) = call.timer_id {
                async_utils::clear_timeout_global(timer_id);
            }

            let msg_type = js_sys::Reflect::get(&data, &"type".into())
                .ok()
                .and_then(|v| v.as_string())
                .unwrap_or_default();
            if msg_type == "error" {
                let message = js_sys::Reflect::get(&data, &"error".into())
                    .unwrap_or_else(|_| JsValue::from_str("worker reported an error"));
                let _ = call.reject.call1(&JsValue::NULL, &message);
            } else {
                let _ = call.resolve.call1(&JsValue::NULL, &data);
            }
        }) as Box<dyn FnMut(_)>);
    worker.set_onmessage(Some(on_message_closure.as_ref().unchecked_ref()));

    let on_error_pending = pending.clone();
    let on_error_closure: OnErrorClosure =
        Closure::wrap(Box::new(move |event: web_sys::ErrorEvent| {
            let message = event.message();
            for call in on_error_pending.borrow_mut().drain().map(|(_, c)| c) {
                if let Some(timer_id) = call.timer_id {
                    async_utils::clear_timeout_global(timer_id);
                }
                let _ = call
                    .reject
                    .call1(&JsValue::NULL, &JsValue::from_str(&message));
            }
        }) as Box<dyn FnMut(_)>);
    worker.set_onerror(Some(on_error_closure.as_ref().unchecked_ref()));

    *worker_slot.borrow_mut() = Some(worker);
    *on_message_slot.borrow_mut() = Some(on_message_closure);
    *on_error_slot.borrow_mut() = Some(on_error_closure);
    Ok(())
}

// Every real code path in this module touches `web_sys::Worker`/`Blob`/`Url`
// or `js_sys::Object`/`Promise`, all of which panic outside a wasm32 + JS
// host runtime (verified empirically -- see `async_utils`'s test comments),
// so the whole test module is gated to wasm32 -- like the existing
// `WorkerPool` tests in `js_api::worker_support` -- rather than gating each
// `#[test]` individually, which would leave `use super::*` unused (and
// therefore fail a native `-D warnings` build) on non-wasm32 targets.
// `wasm-pack` browser tests are intentionally out of scope for this change
// (see the module docs); these tests exist so the type-level contracts are
// checked by *some* automated test the moment a suitable wasm32 JS runner
// is wired up, rather than only being exercised manually.
#[cfg(all(test, target_arch = "wasm32"))]
mod tests {
    use super::*;

    #[test]
    fn test_solve_without_worker_does_not_panic() {
        // `new()` always spawns a worker; simulate the "worker missing"
        // guard path (e.g. after a failed respawn) by clearing the
        // private `worker` field directly -- `tests` is a child module of
        // `preemptible_worker`, so it can see private fields.
        let solver = PreemptibleSolver::new(
            "./nixie_wasm.js".to_string(),
            "./nixie_wasm_bg.wasm".to_string(),
        )
        .expect("worker spawn should succeed in a JS host with Worker/Blob/Url support");
        if let Some(w) = solver.worker.borrow_mut().take() {
            w.terminate();
        }
        assert!(!solver.is_ready());

        // `solve()` with no worker must construct and return a rejected
        // promise rather than hang or panic.
        let _ = solver.solve("(check-sat)".to_string());
    }

    #[test]
    fn test_reject_all_pending_clears_map() {
        let pending: Rc<RefCell<HashMap<u32, PendingCall>>> = Rc::new(RefCell::new(HashMap::new()));
        let promise = Promise::new(&mut |resolve, reject| {
            pending.borrow_mut().insert(
                0,
                PendingCall {
                    resolve,
                    reject,
                    timer_id: None,
                },
            );
        });
        let _ = promise;
        assert_eq!(pending.borrow().len(), 1);
        reject_all_pending(&pending, "test teardown");
        assert!(pending.borrow().is_empty());
    }

    #[test]
    fn test_spawn_worker_into_populates_slots() {
        let worker: Rc<RefCell<Option<web_sys::Worker>>> = Rc::new(RefCell::new(None));
        let on_message: Rc<RefCell<Option<OnMessageClosure>>> = Rc::new(RefCell::new(None));
        let on_error: Rc<RefCell<Option<OnErrorClosure>>> = Rc::new(RefCell::new(None));
        let pending: Rc<RefCell<HashMap<u32, PendingCall>>> = Rc::new(RefCell::new(HashMap::new()));

        let result = spawn_worker_into(
            &worker,
            &on_message,
            &on_error,
            &pending,
            "./nixie_wasm.js",
            "./nixie_wasm_bg.wasm",
        );
        assert!(result.is_ok());
        assert!(worker.borrow().is_some());
        assert!(on_message.borrow().is_some());
        assert!(on_error.borrow().is_some());

        // Clean up the spawned worker so the test does not leak a
        // background thread.
        if let Some(w) = worker.borrow_mut().take() {
            w.terminate();
        }
    }
}
