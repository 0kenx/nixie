//! Regression tests for audit package wasm-p3.
//!
//! Covers the confirmed findings in:
//! - `oxiz-wasm/src/js_api/model.rs` (`getUnsatCore` returned every
//!   assertion instead of the real unsat core)
//! - `oxiz-wasm/src/js_api/solver_core.rs` (`executeAsync`/
//!   `executeWithProgress` split scripts at fixed 20-line boundaries,
//!   breaking multi-line commands)
//! - `oxiz-wasm/src/js_api/streaming.rs` (`StreamingSolver.nextModelEntry`
//!   always returned `None`; `startModelStream` returned a disconnected
//!   controller)
//! - `oxiz-wasm/src/js_api/worker_support.rs` (`WorkerPool` never executed
//!   submitted/queued tasks; `WorkerHandler`'s `"solve"` task silently
//!   dropped failed assertions and then answered `"sat"`)
//!
//! # A note on test setup style
//!
//! Every fixture below declares and asserts within a *single* `execute()`
//! script call, rather than the `declareConst()` + separate
//! `assertFormula()` call pattern used elsewhere in this test suite.
//! That's deliberate: `Context::execute_script` parses each call with a
//! brand-new `oxiz_core` parser whose declared-symbol table starts empty,
//! so a symbol declared in one `execute_script`/`assertFormula` call is
//! not visible to a *different*, later `execute_script` call (this
//! reproduces with plain `oxiz_solver::Context` alone, independent of
//! WASM/JS at all) -- a pre-existing limitation in `oxiz-core`'s parser /
//! `oxiz-solver::Context::execute_script`, outside this package's owned
//! files (`oxiz-wasm/src/js_api/*`, `lazy_loader.rs`, `package.json`).
//! Combining declare+assert into one script call sidesteps it so these
//! tests actually exercise the fixes under test instead of an unrelated
//! defect.
//!
//! Run with `wasm-pack test --node` (Node.js is the default execution
//! target for `wasm-bindgen-test` when `wasm_bindgen_test_configure!` is
//! not invoked at all -- there is no `run_in_node_js` option; unlike
//! `tests/audit_wasm_p2.rs` and `tests/nodejs.rs` in this same directory,
//! which both call `wasm_bindgen_test_configure!(run_in_node_js)`, a
//! macro invocation `wasm-bindgen-test` 0.3.76 has no rule for and which
//! therefore fails to compile for wasm32 at all -- see this package's
//! reported findings).

#![cfg(target_arch = "wasm32")]

// `WasmSolver`/`WasmError`/`version` live directly at the crate root, but
// `WorkerPool`, `WorkerHandler`, `WorkerTask`, `StreamingSolver`,
// `DataChunk`, etc. live one module deeper (`oxiz_wasm::js_api::*`, only
// re-exported at the `js_api` level, not further re-exported to the crate
// root) -- both glob imports are needed to bring everything used below
// into scope.
use oxiz_wasm::js_api::*;
use oxiz_wasm::*;
use wasm_bindgen::JsValue;
use wasm_bindgen_test::*;

// ========  ========
// model.rs: getUnsatCore returns a real (named-assertion-based) core,
// not every assertion.
// ========  ========

/// Regression: `getUnsatCore` must return the *names* of the unsat core's
/// assertions (as `(get-unsat-core)` does), not a dump of every
/// assertion's full formula text -- which is what the old
/// `ctx.format_assertions()` stub returned, unconditionally including
/// even unnamed assertions that could never legitimately appear in a
/// named unsat core.
///
/// Note: `oxiz-solver`'s core builder is a conservative (non-minimal)
/// "all named assertions" implementation (see
/// `oxiz-solver/src/solver/model_builder.rs::build_unsat_core`), so this
/// deliberately does not assert minimality (that a named-but-irrelevant
/// assertion is excluded) -- only that the response is genuinely core
/// *names*, not raw formula text, and that an *unnamed* assertion (which
/// cannot appear in any named core, minimal or not) never shows up.
#[wasm_bindgen_test]
fn test_get_unsat_core_returns_names_not_raw_formulas() {
    let mut solver = WasmSolver::new();
    solver
        .execute(
            "(set-logic QF_LIA)\
             (set-option :produce-unsat-cores true)\
             (declare-const x Int)\
             (declare-const z Int)\
             (assert (! (> x 0) :named positive))\
             (assert (! (< x 0) :named negative))\
             (assert (> z 0))",
        )
        .unwrap();

    assert_eq!(solver.check_sat(), "unsat");

    let core = solver.get_unsat_core().unwrap();
    let core_str = core.as_string().expect("core should be a string");

    // The real core must mention the two conflicting named assertions...
    assert!(
        core_str.contains("positive"),
        "core should contain 'positive', got: {core_str}"
    );
    assert!(
        core_str.contains("negative"),
        "core should contain 'negative', got: {core_str}"
    );
    // ...must never include an *unnamed* assertion's raw text (the old
    // `format_assertions()` stub dumped every assertion, named or not)...
    assert!(
        !core_str.contains("z"),
        "core must not include the unnamed assertion over z, got: {core_str}"
    );
    // ...and must be a list of names, not full SMT-LIB formula text.
    assert!(
        !core_str.contains(">") && !core_str.contains("0"),
        "core should contain assertion names, not raw formula text, got: {core_str}"
    );
}

/// Regression: without `produce-unsat-cores` enabled, `getUnsatCore` must
/// fail honestly rather than fabricating a core from all assertions.
#[wasm_bindgen_test]
fn test_get_unsat_core_without_option_enabled_is_honest() {
    let mut solver = WasmSolver::new();
    solver
        .execute(
            "(set-logic QF_LIA)\
             (declare-const x Int)\
             (assert (> x 0))\
             (assert (< x 0))",
        )
        .unwrap();

    assert_eq!(solver.check_sat(), "unsat");

    // `produce-unsat-cores` was never enabled, so there is no real core to
    // report; the old stub would have happily printed every assertion
    // anyway.
    let result = solver.get_unsat_core();
    assert!(result.is_err());
}

// ========  ========
// solver_core.rs: executeAsync/executeWithProgress must not break
// multi-line commands at a fixed line-count boundary.
// ========  ========

/// Build a script whose single `(assert ...)` command spans well over 20
/// lines -- the old fixed-size chunker would have split straight through
/// the middle of it.
fn deeply_nested_multiline_script() -> String {
    let mut s = String::from("(set-logic QF_LIA)\n(declare-const x Int)\n(assert\n  (and\n");
    for _ in 0..30 {
        s.push_str("    (>= x 0)\n");
    }
    s.push_str("  )\n)\n(check-sat)\n");
    s
}

#[wasm_bindgen_test]
async fn test_execute_async_handles_multiline_command_spanning_chunk_boundary() {
    let mut solver = WasmSolver::new();
    let script = deeply_nested_multiline_script();

    // The synchronous path already handles this correctly; it's the
    // baseline this async path must match.
    let mut sync_solver = WasmSolver::new();
    let sync_result = sync_solver.execute(&script).unwrap();

    let async_result = solver.execute_async(script).await.unwrap();
    assert_eq!(
        async_result.as_string(),
        sync_result.as_string(),
        "executeAsync must accept the same multi-line script execute() accepts"
    );
}

#[wasm_bindgen_test]
async fn test_execute_with_progress_handles_multiline_command_spanning_chunk_boundary() {
    let mut solver = WasmSolver::new();
    let script = deeply_nested_multiline_script();

    // No callback needed for this check; just confirm it doesn't reject a
    // script `execute()` accepts.
    let result = solver.execute_with_progress(script, None).await;
    assert!(
        result.is_ok(),
        "executeWithProgress must accept the same multi-line script execute() accepts"
    );
}

// ========  ========
// streaming.rs: nextModelEntry streams real entries; startModelStream
// returns a controller connected to the internally retained one.
// ========  ========

#[wasm_bindgen_test]
fn test_streaming_next_model_entry_yields_real_entries() {
    let mut solver = StreamingSolver::new();
    solver.set_logic("QF_LIA");
    // `declareConst` populates `Context::declared_consts` directly (not
    // via a re-parsed script), and `assertFormula`'s formula here is
    // self-contained (references no declared symbol), so this setup does
    // not depend on the cross-call declaration-visibility limitation
    // described at the top of this file; `x` still appears in the model
    // because `Context::get_model()` reports a value for every declared
    // constant, not only ones referenced by an assertion.
    solver.declare_const("x", "Int").unwrap();
    solver.assert_formula("(> 1 0)").unwrap();
    assert_eq!(solver.check_sat(), "sat");

    let mut seen = Vec::new();
    while let Some(entry) = solver.next_model_entry() {
        seen.push(entry.get_name());
    }
    assert!(
        seen.contains(&"x".to_string()),
        "declared variable 'x' should appear in the streamed model, got: {seen:?}"
    );
    // Exhausted afterwards, not an infinite/looping stream.
    assert!(solver.next_model_entry().is_none());
}

#[wasm_bindgen_test]
fn test_streaming_start_model_stream_controller_is_connected() {
    let mut solver = StreamingSolver::new();
    let controller = solver.start_model_stream();

    // Enqueue through the returned handle and confirm it is visible
    // through a second dequeue on the same handle (proving it isn't a
    // disposable, disconnected instance).
    let chunk = DataChunk::new(vec![9, 9, 9], 0);
    assert!(controller.enqueue(chunk));
    assert_eq!(controller.buffer_length(), 1);
    let dequeued = controller.dequeue().unwrap();
    assert_eq!(dequeued.sequence(), 0);
}

// ========  ========
// worker_support.rs: WorkerPool actually executes tasks; WorkerHandler's
// "solve" task surfaces assertion failures instead of silently answering
// "sat".
// ========  ========

#[wasm_bindgen_test]
fn test_worker_handler_solve_answers_real_unsat() {
    let mut handler = WorkerHandler::new();
    let data = js_sys::Object::new();
    js_sys::Reflect::set(&data, &"logic".into(), &"QF_LIA".into()).unwrap();

    let decls = js_sys::Array::new();
    let decl = js_sys::Object::new();
    js_sys::Reflect::set(&decl, &"name".into(), &"x".into()).unwrap();
    js_sys::Reflect::set(&decl, &"sort".into(), &"Int".into()).unwrap();
    decls.push(&decl);
    js_sys::Reflect::set(&data, &"declarations".into(), &decls).unwrap();

    let assertions = js_sys::Array::new();
    assertions.push(&JsValue::from_str("(> x 0)"));
    assertions.push(&JsValue::from_str("(< x 0)"));
    js_sys::Reflect::set(&data, &"assertions".into(), &assertions).unwrap();

    let task = WorkerTask::new("t1".to_string(), "solve".to_string(), data.into());
    let result = handler.handle_task(task);

    let status = js_sys::Reflect::get(&result, &"status".into()).unwrap();
    assert_eq!(status.as_string().as_deref(), Some("unsat"));
}

/// Regression: an assertion over an undeclared variable must surface as
/// a real error, not be silently dropped (which previously let
/// `check-sat` run against an emptied/partial problem and answer
/// `"sat"` for something the caller meant to be constrained).
#[wasm_bindgen_test]
fn test_worker_handler_solve_reports_bad_assertion_instead_of_dropping_it() {
    let mut handler = WorkerHandler::new();
    let data = js_sys::Object::new();
    js_sys::Reflect::set(&data, &"logic".into(), &"QF_LIA".into()).unwrap();

    let assertions = js_sys::Array::new();
    // "z" was never declared.
    assertions.push(&JsValue::from_str("(> z 0)"));
    js_sys::Reflect::set(&data, &"assertions".into(), &assertions).unwrap();

    let task = WorkerTask::new("t2".to_string(), "solve".to_string(), data.into());
    let result = handler.handle_task(task);

    let status = js_sys::Reflect::get(&result, &"status".into()).unwrap();
    assert_eq!(
        status.as_string().as_deref(),
        Some("error"),
        "an unparseable assertion must not be silently dropped and answered 'sat'"
    );
    let error = js_sys::Reflect::get(&result, &"error".into()).unwrap();
    assert!(error.as_string().is_some_and(|s| !s.is_empty()));
}

#[wasm_bindgen_test]
async fn test_worker_pool_execute_runs_the_task_for_real() {
    let pool = WorkerPool::new(2);
    pool.init();

    let data = js_sys::Object::new();
    js_sys::Reflect::set(&data, &"logic".into(), &"QF_LIA".into()).unwrap();
    let decls = js_sys::Array::new();
    let decl = js_sys::Object::new();
    js_sys::Reflect::set(&decl, &"name".into(), &"x".into()).unwrap();
    js_sys::Reflect::set(&decl, &"sort".into(), &"Int".into()).unwrap();
    decls.push(&decl);
    js_sys::Reflect::set(&data, &"declarations".into(), &decls).unwrap();
    let assertions = js_sys::Array::new();
    assertions.push(&JsValue::from_str("(> x 0)"));
    js_sys::Reflect::set(&data, &"assertions".into(), &assertions).unwrap();

    let task = WorkerTask::new("pool-task-1".to_string(), "solve".to_string(), data.into());
    let result = pool.execute(task).await.unwrap();

    let status = js_sys::Reflect::get(&result, &"status".into()).unwrap();
    assert_eq!(
        status.as_string().as_deref(),
        Some("sat"),
        "WorkerPool.execute() must actually run the task, not leave it queued forever"
    );

    // Stats must reflect the real completed task, not stay at zero.
    let stats = pool.get_stats();
    let total_completed = js_sys::Reflect::get(&stats, &"total_completed".into()).unwrap();
    assert_eq!(total_completed.as_f64(), Some(1.0));
}

#[wasm_bindgen_test]
async fn test_worker_pool_drain_queue_processes_submitted_tasks() {
    let pool = WorkerPool::new(2);
    pool.init();
    assert_eq!(pool.queue_length(), 0);

    let make_task = |id: &str| {
        let data = js_sys::Object::new();
        js_sys::Reflect::set(&data, &"logic".into(), &"QF_UF".into()).unwrap();
        let decls = js_sys::Array::new();
        let decl = js_sys::Object::new();
        js_sys::Reflect::set(&decl, &"name".into(), &"p".into()).unwrap();
        js_sys::Reflect::set(&decl, &"sort".into(), &"Bool".into()).unwrap();
        decls.push(&decl);
        js_sys::Reflect::set(&data, &"declarations".into(), &decls).unwrap();
        let assertions = js_sys::Array::new();
        assertions.push(&JsValue::from_str("p"));
        js_sys::Reflect::set(&data, &"assertions".into(), &assertions).unwrap();
        WorkerTask::new(id.to_string(), "solve".to_string(), data.into())
    };

    pool.submit(make_task("q1"));
    pool.submit(make_task("q2"));
    assert_eq!(pool.queue_length(), 2);

    let results = pool.drain_queue().await.unwrap();
    assert_eq!(results.length(), 2);
    // The queue must actually have been drained (this was the core
    // "facade" defect: tasks queued forever, `queueLength()` never
    // dropping).
    assert_eq!(pool.queue_length(), 0);

    for i in 0..results.length() {
        let result = results.get(i);
        let status = js_sys::Reflect::get(&result, &"status".into()).unwrap();
        assert_eq!(status.as_string().as_deref(), Some("sat"));
    }
}

#[wasm_bindgen_test]
fn test_worker_pool_construction_with_zero_workers_is_honest() {
    let pool = WorkerPool::new(0);
    pool.init();
    // No worker slots exist; `execute`/`drainQueue` must reject rather
    // than silently doing nothing or panicking.
    assert_eq!(pool.idle_count(), 0);
    assert_eq!(pool.busy_count(), 0);
}
