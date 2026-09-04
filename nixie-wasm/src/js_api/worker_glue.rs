//! Generates the JS bootstrap glue for running the Nixie solver inside a
//! dedicated Web Worker.
//!
//! wasm-bindgen cannot generate a Worker's *entry* script for you: the
//! very first thing that runs in a fresh Worker context must be ordinary
//! JS that fetches/instantiates the wasm module -- compiled WASM has no
//! way to bootstrap itself. This module generates that small script from
//! Rust so it always stays in lock-step with the message protocol
//! implemented by
//! [`crate::js_api::worker_support::WorkerHandler::handle_message`] --
//! the same "the Rust source is the single source of truth" pattern
//! [`crate::js_api::typescript`] uses for the generated `.d.ts` file.
//!
//! [`crate::js_api::preemptible_worker::PreemptibleSolver`] calls
//! [`generate_worker_bootstrap_js`] internally (turning the result into a
//! `Blob` URL), so most consumers never need to call it directly. It is
//! exported so a build step can also write it to a real `.js` file on
//! disk if a Blob-URL worker is undesirable (e.g. to satisfy a strict
//! `worker-src` CSP that only allows same-origin script URLs).
//!
//! # Message protocol
//!
//! Requests sent to the worker (`worker.postMessage(...)`):
//! `{ id, type: "init" | "solve" | "cancel" | "shutdown", data?: {...} }`
//!
//! Responses received from the worker (`worker.onmessage`):
//! `{ id, type: "result" | "error", status?, ... }`
//!
//! See [`crate::js_api::worker_support::WorkerHandler::handle_message`]
//! for the exact fields `data`/the result object carry for each message
//! type, and [`crate::js_api::cancellation::CancellationToken`] for the
//! optional `data.cancellationBuffer` (a `SharedArrayBuffer`) that enables
//! cooperative cancellation.
//!
//! # Timeout semantics (read before relying on the "cancel" message)
//!
//! This bootstrap script has **no idea it is being timed**. Hard
//! preemption is done from the MAIN thread, outside this script entirely,
//! by calling `worker.terminate()` (see
//! [`crate::js_api::preemptible_worker::PreemptibleSolver`]) -- a worker
//! cannot terminate its own synchronous WASM execution. The `"cancel"`
//! message type and the optional `data.cancellationBuffer` are both
//! **cooperative only**: they are observed by `WorkerHandler` at call
//! points between operations, never in the middle of a single in-flight
//! `check_sat` call. Do not rely on either for a hard guarantee.

#![forbid(unsafe_code)]

use wasm_bindgen::prelude::*;

/// Generate the worker-side bootstrap script.
///
/// Requires a `--target no-modules` (classic-script) wasm-bindgen build:
/// the script loads the glue via `importScripts()` and calls the
/// resulting global `wasm_bindgen` init function. This crate deliberately
/// does not use an ES-module (`{ type: "module" }`) worker here, because
/// Blob-URL module workers have inconsistent MIME-type/CORS behavior
/// across browsers, whereas classic Blob-URL workers are broadly and
/// consistently supported.
///
/// * `wasm_js_url` -- URL of the generated `<name>.js` glue file (the
///   same one the main thread itself loaded, or an equivalent
///   `--target no-modules` build of it).
/// * `wasm_bg_url` -- URL of the generated `<name>_bg.wasm` binary.
#[wasm_bindgen(js_name = generateWorkerBootstrapJs)]
pub fn generate_worker_bootstrap_js(wasm_js_url: &str, wasm_bg_url: &str) -> String {
    format!(
        r#"// Nixie WASM -- generated Worker bootstrap.
// Source of truth: nixie_wasm::js_api::worker_glue::generate_worker_bootstrap_js()
// Do not hand-edit; regenerate from Rust if the message protocol changes.
//
// Message protocol (see WorkerHandler::handleMessage):
//   in:  {{ id, type: "init" | "solve" | "cancel" | "shutdown", data?: {{...}} }}
//   out: {{ id, type: "result" | "error", status?, ... }}
//
// Timeout semantics: this worker has NO idea it is being timed. Hard
// preemption is performed from the MAIN thread by calling
// `worker.terminate()` (see PreemptibleSolver); this script cannot and
// does not implement that itself. The "cancel" message type and the
// optional `data.cancellationBuffer` (a SharedArrayBuffer) are both
// COOPERATIVE only: WorkerHandler observes them at call points between
// operations, never inside a single in-flight `check_sat`.
importScripts({wasm_js_url:?});

const {{ WorkerHandler, default: init }} = wasm_bindgen;

let handler = null;
let initPromise = null;

async function ensureHandler() {{
    if (!initPromise) {{
        initPromise = init({wasm_bg_url:?}).then(() => {{
            handler = new WorkerHandler();
        }});
    }}
    await initPromise;
    return handler;
}}

self.onmessage = async function (event) {{
    const msg = event.data || {{}};
    try {{
        const h = await ensureHandler();
        const result = h.handleMessage(msg);
        postMessage(result);
    }} catch (error) {{
        postMessage({{
            id: msg.id,
            type: "error",
            error: error && error.message ? error.message : String(error),
        }});
    }}
}};
"#,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bootstrap_embeds_both_urls() {
        let js = generate_worker_bootstrap_js("./nixie_wasm.js", "./nixie_wasm_bg.wasm");
        assert!(js.contains("./nixie_wasm.js"), "missing glue URL");
        assert!(
            js.contains("./nixie_wasm_bg.wasm"),
            "missing wasm binary URL"
        );
    }

    #[test]
    fn test_bootstrap_uses_importscripts_and_handle_message() {
        let js = generate_worker_bootstrap_js("a.js", "a_bg.wasm");
        assert!(
            js.contains("importScripts("),
            "must use classic-worker loading"
        );
        assert!(
            js.contains("h.handleMessage(msg)"),
            "must dispatch through WorkerHandler::handle_message"
        );
        assert!(js.contains("new WorkerHandler()"));
    }

    #[test]
    fn test_bootstrap_documents_hard_vs_cooperative_timeout() {
        let js = generate_worker_bootstrap_js("a.js", "a_bg.wasm");
        assert!(
            js.contains("COOPERATIVE"),
            "must call out that in-script cancellation is cooperative only"
        );
        assert!(
            js.contains("terminate()"),
            "must point to the hard-preemption mechanism"
        );
    }

    #[test]
    fn test_bootstrap_escapes_url_with_special_characters() {
        // URLs can legitimately contain query strings; make sure the
        // generated script stays syntactically valid JS (the embedded
        // strings must be properly quoted/escaped, not string-concatenated
        // in a way that could break out of the literal).
        let js = generate_worker_bootstrap_js("./pkg/a.js?v=1", "./pkg/a_bg.wasm?v=1");
        assert!(js.contains(r#"importScripts("./pkg/a.js?v=1")"#));
        assert!(js.contains(r#"init("./pkg/a_bg.wasm?v=1")"#));
    }
}
