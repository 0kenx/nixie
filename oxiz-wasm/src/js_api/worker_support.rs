//! Web Worker Support for Background Solving
#![allow(
    clippy::should_implement_trait,
    clippy::explicit_counter_loop,
    dead_code
)] // WASM constraints
//!
//! This module provides utilities for running OxiZ solver operations
//! in Web Workers, enabling background computation without blocking
//! the main UI thread.
//!
//! # Architecture
//!
//! - **Worker Pool**: Manage multiple worker threads
//! - **Message Passing**: Structured communication protocol
//! - **Task Queue**: Queue solver tasks for processing
//! - **Result Streaming**: Stream results back to main thread
//!
//! # Example (Main Thread)
//!
//! ```javascript
//! const pool = new WorkerPool(4); // 4 workers
//!
//! const task = {
//!     type: 'solve',
//!     logic: 'QF_LIA',
//!     assertions: ['(> x 0)', '(< x 10)']
//! };
//!
//! const result = await pool.execute(task);
//! console.log(result.status); // "sat" or "unsat"
//! ```
//!
//! # Example (Worker Thread)
//!
//! ```javascript
//! import { WorkerHandler } from '@cooljapan/oxiz/worker';
//!
//! const handler = new WorkerHandler();
//! handler.start();
//! ```

#![forbid(unsafe_code)]

use crate::async_utils;
use crate::js_api::cancellation::CancellationToken;
use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;
use wasm_bindgen::JsCast;
use wasm_bindgen::prelude::*;

/// Current time in milliseconds, or `0.0` outside a browser `window`
/// (e.g. native tests, non-browser JS runtimes without `performance`).
fn now_ms() -> f64 {
    web_sys::window()
        .and_then(|w| w.performance())
        .map(|p| p.now())
        .unwrap_or(0.0)
}

/// Message types for worker communication
#[wasm_bindgen]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorkerMessageType {
    /// Initialize worker
    Init,
    /// Execute a task
    Execute,
    /// Cancel a task
    Cancel,
    /// Shutdown worker
    Shutdown,
    /// Task result
    Result,
    /// Task error
    Error,
    /// Progress update
    Progress,
    /// Heartbeat
    Heartbeat,
}

impl WorkerMessageType {
    /// Get message type name
    pub fn name(&self) -> &'static str {
        match self {
            WorkerMessageType::Init => "init",
            WorkerMessageType::Execute => "execute",
            WorkerMessageType::Cancel => "cancel",
            WorkerMessageType::Shutdown => "shutdown",
            WorkerMessageType::Result => "result",
            WorkerMessageType::Error => "error",
            WorkerMessageType::Progress => "progress",
            WorkerMessageType::Heartbeat => "heartbeat",
        }
    }

    /// Parse from string
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "init" => Some(WorkerMessageType::Init),
            "execute" => Some(WorkerMessageType::Execute),
            "cancel" => Some(WorkerMessageType::Cancel),
            "shutdown" => Some(WorkerMessageType::Shutdown),
            "result" => Some(WorkerMessageType::Result),
            "error" => Some(WorkerMessageType::Error),
            "progress" => Some(WorkerMessageType::Progress),
            "heartbeat" => Some(WorkerMessageType::Heartbeat),
            _ => None,
        }
    }
}

/// Worker task
#[wasm_bindgen]
pub struct WorkerTask {
    /// Task ID
    id: String,
    /// Task type
    task_type: String,
    /// Task data (JSON)
    data: JsValue,
    /// Priority (higher = more important)
    priority: u32,
    /// Timeout in milliseconds
    timeout_ms: Option<u32>,
}

#[wasm_bindgen]
impl WorkerTask {
    /// Create a new worker task
    #[wasm_bindgen(constructor)]
    pub fn new(id: String, task_type: String, data: JsValue) -> Self {
        Self {
            id,
            task_type,
            data,
            priority: 0,
            timeout_ms: None,
        }
    }

    /// Set priority
    #[wasm_bindgen(js_name = withPriority)]
    pub fn with_priority(mut self, priority: u32) -> Self {
        self.priority = priority;
        self
    }

    /// Set timeout
    #[wasm_bindgen(js_name = withTimeout)]
    pub fn with_timeout(mut self, timeout_ms: u32) -> Self {
        self.timeout_ms = Some(timeout_ms);
        self
    }

    /// Get task ID
    #[wasm_bindgen(js_name = getId)]
    pub fn get_id(&self) -> String {
        self.id.clone()
    }

    /// Get task type
    #[wasm_bindgen(js_name = getType)]
    pub fn get_type(&self) -> String {
        self.task_type.clone()
    }

    /// Get task data
    #[wasm_bindgen(js_name = getData)]
    pub fn get_data(&self) -> JsValue {
        self.data.clone()
    }

    /// Export as JS object
    #[wasm_bindgen(js_name = toObject)]
    pub fn to_object(&self) -> JsValue {
        let obj = js_sys::Object::new();
        let _ = js_sys::Reflect::set(&obj, &"id".into(), &self.id.clone().into());
        let _ = js_sys::Reflect::set(&obj, &"type".into(), &self.task_type.clone().into());
        let _ = js_sys::Reflect::set(&obj, &"data".into(), &self.data);
        let _ = js_sys::Reflect::set(&obj, &"priority".into(), &self.priority.into());
        if let Some(timeout) = self.timeout_ms {
            let _ = js_sys::Reflect::set(&obj, &"timeout_ms".into(), &timeout.into());
        }
        obj.into()
    }
}

/// Worker status
#[wasm_bindgen]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorkerStatus {
    /// Worker is idle
    Idle,
    /// Worker is busy
    Busy,
    /// Worker is starting
    Starting,
    /// Worker is stopping
    Stopping,
    /// Worker has failed
    Failed,
}

impl WorkerStatus {
    /// Get status name
    pub fn name(&self) -> &'static str {
        match self {
            WorkerStatus::Idle => "idle",
            WorkerStatus::Busy => "busy",
            WorkerStatus::Starting => "starting",
            WorkerStatus::Stopping => "stopping",
            WorkerStatus::Failed => "failed",
        }
    }
}

/// Worker info
struct WorkerInfo {
    id: usize,
    status: WorkerStatus,
    current_task: Option<String>,
    tasks_completed: usize,
    tasks_failed: usize,
    total_time_ms: f64,
    created_at: f64,
}

/// Worker pool for managing multiple workers
///
/// # Threading model (honest disclosure)
///
/// OxiZ WASM does not enable the `atomics`/`bulk-memory` wasm target
/// features and does not ship a browser `Worker` bootstrap script, so
/// there is no real OS/browser-thread parallelism available here – the
/// crate is built and used as an ordinary single-threaded WASM module.
/// Rather than have `submit()` enqueue tasks that are never drained (a
/// facade that silently loses work), `WorkerPool` round-robins submitted
/// tasks across `worker_count` independent solver slots and executes
/// them for real, cooperatively, on the calling thread – yielding to the
/// JS event loop between tasks so the UI stays responsive. Every result
/// returned by `execute()`/`drainQueue()` comes from actually running the
/// task through a real [`WorkerHandler`], never a fabricated answer.
#[wasm_bindgen]
pub struct WorkerPool {
    /// Worker info
    workers: Rc<RefCell<HashMap<usize, WorkerInfo>>>,
    /// Task queue (drained by `drainQueue()`)
    queue: Rc<RefCell<VecDeque<WorkerTask>>>,
    /// Next worker ID
    next_id: Rc<RefCell<usize>>,
    /// Number of workers
    worker_count: usize,
    /// Enable verbose logging
    verbose: bool,
    /// Per-slot solver handlers that actually execute submitted tasks.
    handlers: Rc<RefCell<Vec<WorkerHandler>>>,
    /// Round-robin cursor into `handlers`
    next_handler: Rc<RefCell<usize>>,
}

#[wasm_bindgen]
impl WorkerPool {
    /// Create a new worker pool
    ///
    /// `worker_count` independent solver slots are provisioned
    /// immediately (there is no separate async "spawn" step since no
    /// real OS/browser threads are created); call [`WorkerPool::init`]
    /// to populate the reporting/stats bookkeeping.
    #[wasm_bindgen(constructor)]
    pub fn new(worker_count: usize) -> Self {
        let handlers = (0..worker_count).map(|_| WorkerHandler::new()).collect();
        Self {
            workers: Rc::new(RefCell::new(HashMap::new())),
            queue: Rc::new(RefCell::new(VecDeque::new())),
            next_id: Rc::new(RefCell::new(0)),
            worker_count,
            verbose: false,
            handlers: Rc::new(RefCell::new(handlers)),
            next_handler: Rc::new(RefCell::new(0)),
        }
    }

    /// Initialize workers
    ///
    /// Populates worker bookkeeping (id/status/stats) if it has not been
    /// populated yet, and marks every worker `Idle` (ready to execute)
    /// since solver slots are already provisioned by the constructor.
    /// Safe to call more than once (idempotent): it will not create
    /// duplicate entries, it simply resets existing ones back to `Idle`.
    #[wasm_bindgen(js_name = init)]
    pub fn init(&self) {
        let current_time = now_ms();
        let mut workers = self.workers.borrow_mut();

        if workers.is_empty() {
            for _ in 0..self.worker_count {
                let id = self.get_next_id();
                workers.insert(
                    id,
                    WorkerInfo {
                        id,
                        status: WorkerStatus::Idle,
                        current_task: None,
                        tasks_completed: 0,
                        tasks_failed: 0,
                        total_time_ms: 0.0,
                        created_at: current_time,
                    },
                );
            }
        } else {
            for info in workers.values_mut() {
                if info.status != WorkerStatus::Failed {
                    info.status = WorkerStatus::Idle;
                    info.current_task = None;
                }
            }
        }
        drop(workers);

        if self.verbose {
            web_sys::console::log_1(
                &format!("Initialized worker pool with {} workers", self.worker_count).into(),
            );
        }
    }

    /// Submit a task to the queue for later batch processing via
    /// [`WorkerPool::drain_queue`].
    ///
    /// For immediate execution of a single task, prefer
    /// [`WorkerPool::execute`].
    #[wasm_bindgen(js_name = submit)]
    pub fn submit(&self, task: WorkerTask) {
        self.queue.borrow_mut().push_back(task);

        if self.verbose {
            web_sys::console::log_1(
                &format!("Task queued, queue length: {}", self.queue_length()).into(),
            );
        }
    }

    /// Execute a single task immediately (bypassing the queue) using the
    /// next available (round-robin) solver slot, and return the real
    /// result object produced by that slot's [`WorkerHandler`].
    ///
    /// # Errors
    ///
    /// Rejects if the pool has zero worker slots (constructed with
    /// `worker_count == 0`).
    #[wasm_bindgen(js_name = execute)]
    pub async fn execute(&self, task: WorkerTask) -> Result<JsValue, JsValue> {
        if self.handlers.borrow().is_empty() {
            return Err(JsValue::from_str(
                "WorkerPool has no worker slots (constructed with worker_count == 0)",
            ));
        }
        // Yield once so this genuinely goes through a microtask/event-loop
        // turn rather than always resolving fully synchronously.
        async_utils::yield_now().await;
        Ok(self.run_one(task))
    }

    /// Drain and execute every task currently queued by [`WorkerPool::submit`],
    /// in FIFO order, round-robined across worker slots. Yields to the
    /// event loop between tasks to keep the UI responsive. Returns the
    /// real result objects, in submission order.
    #[wasm_bindgen(js_name = drainQueue)]
    pub async fn drain_queue(&self) -> Result<js_sys::Array, JsValue> {
        if self.handlers.borrow().is_empty() && !self.queue.borrow().is_empty() {
            return Err(JsValue::from_str(
                "WorkerPool has no worker slots (constructed with worker_count == 0)",
            ));
        }

        let results = js_sys::Array::new();
        let mut processed = 0usize;
        loop {
            let task = self.queue.borrow_mut().pop_front();
            let Some(task) = task else { break };

            results.push(&self.run_one(task));
            processed += 1;
            if processed.is_multiple_of(4) {
                async_utils::yield_now().await;
            }
        }
        Ok(results)
    }

    /// Run one task to completion on the next round-robin solver slot,
    /// updating worker bookkeeping. Internal helper shared by `execute()`
    /// and `drainQueue()`.
    fn run_one(&self, task: WorkerTask) -> JsValue {
        let handler_count = self.handlers.borrow().len();
        // Guarded by callers, but stay honest rather than panicking/
        // indexing out of bounds if this is ever reached with 0 slots.
        if handler_count == 0 {
            let error = js_sys::Object::new();
            let _ = js_sys::Reflect::set(&error, &"status".into(), &"error".into());
            let _ =
                js_sys::Reflect::set(&error, &"error".into(), &"No worker slots available".into());
            return error.into();
        }

        let slot = {
            let mut next = self.next_handler.borrow_mut();
            let idx = *next % handler_count;
            *next = (*next + 1) % handler_count;
            idx
        };

        self.set_worker_status(slot, WorkerStatus::Busy, Some(task.get_id()));
        let start = now_ms();
        let result = {
            let mut handlers = self.handlers.borrow_mut();
            handlers[slot].handle_task(task)
        };
        let elapsed = now_ms() - start;
        self.record_completion(slot, elapsed, Self::result_is_error(&result));

        if self.verbose {
            web_sys::console::log_1(&format!("Worker {} completed task", slot).into());
        }

        result
    }

    fn result_is_error(result: &JsValue) -> bool {
        if let Ok(status) = js_sys::Reflect::get(result, &"status".into())
            && let Some(s) = status.as_string()
        {
            return s == "error";
        }
        js_sys::Reflect::has(result, &"error".into()).unwrap_or(false)
    }

    fn set_worker_status(
        &self,
        worker_id: usize,
        status: WorkerStatus,
        current_task: Option<String>,
    ) {
        if let Some(info) = self.workers.borrow_mut().get_mut(&worker_id) {
            info.status = status;
            info.current_task = current_task;
        }
    }

    fn record_completion(&self, worker_id: usize, elapsed_ms: f64, failed: bool) {
        if let Some(info) = self.workers.borrow_mut().get_mut(&worker_id) {
            info.status = WorkerStatus::Idle;
            info.current_task = None;
            info.total_time_ms += elapsed_ms;
            if failed {
                info.tasks_failed += 1;
            } else {
                info.tasks_completed += 1;
            }
        }
    }

    /// Get queue length
    #[wasm_bindgen(js_name = queueLength)]
    pub fn queue_length(&self) -> usize {
        self.queue.borrow().len()
    }

    /// Get idle worker count
    #[wasm_bindgen(js_name = idleCount)]
    pub fn idle_count(&self) -> usize {
        self.workers
            .borrow()
            .values()
            .filter(|w| w.status == WorkerStatus::Idle)
            .count()
    }

    /// Get busy worker count
    #[wasm_bindgen(js_name = busyCount)]
    pub fn busy_count(&self) -> usize {
        self.workers
            .borrow()
            .values()
            .filter(|w| w.status == WorkerStatus::Busy)
            .count()
    }

    /// Get worker statistics
    #[wasm_bindgen(js_name = getStats)]
    pub fn get_stats(&self) -> JsValue {
        let stats = js_sys::Object::new();
        let _ = js_sys::Reflect::set(&stats, &"worker_count".into(), &self.worker_count.into());
        let _ = js_sys::Reflect::set(&stats, &"idle_count".into(), &self.idle_count().into());
        let _ = js_sys::Reflect::set(&stats, &"busy_count".into(), &self.busy_count().into());
        let _ = js_sys::Reflect::set(&stats, &"queue_length".into(), &self.queue_length().into());

        let workers = self.workers.borrow();
        let total_completed: usize = workers.values().map(|w| w.tasks_completed).sum();
        let total_failed: usize = workers.values().map(|w| w.tasks_failed).sum();
        let total_time: f64 = workers.values().map(|w| w.total_time_ms).sum();

        let _ = js_sys::Reflect::set(&stats, &"total_completed".into(), &total_completed.into());
        let _ = js_sys::Reflect::set(&stats, &"total_failed".into(), &total_failed.into());
        let _ = js_sys::Reflect::set(&stats, &"total_time_ms".into(), &total_time.into());

        let avg_time = if total_completed > 0 {
            total_time / total_completed as f64
        } else {
            0.0
        };
        let _ = js_sys::Reflect::set(&stats, &"avg_time_ms".into(), &avg_time.into());

        stats.into()
    }

    /// Shutdown all workers
    #[wasm_bindgen(js_name = shutdown)]
    pub fn shutdown(&self) {
        for worker in self.workers.borrow_mut().values_mut() {
            worker.status = WorkerStatus::Stopping;
        }

        if self.verbose {
            web_sys::console::log_1(&"Worker pool shutting down".into());
        }
    }

    /// Enable verbose logging
    #[wasm_bindgen(js_name = setVerbose)]
    pub fn set_verbose(&mut self, verbose: bool) {
        self.verbose = verbose;
    }

    fn get_next_id(&self) -> usize {
        let mut next_id = self.next_id.borrow_mut();
        let id = *next_id;
        *next_id += 1;
        id
    }
}

/// Worker handler for use inside worker threads
///
/// # Two entry points, two different threading contracts
///
/// - [`WorkerHandler::handle_task`] takes a [`WorkerTask`] -- a
///   `wasm_bindgen` class instance. Instances like that cannot cross a
///   real `Worker` boundary (`postMessage` structured-clones plain data
///   only; it cannot clone a pointer into another realm's WASM memory),
///   so this entry point only works when `WorkerHandler` runs
///   cooperatively on the SAME thread as its caller -- exactly what
///   [`WorkerPool`] does.
/// - [`WorkerHandler::handle_message`] takes a plain, structured-clone-
///   safe `JsValue` (a JS object) and is the entry point meant for a real
///   `Worker`'s `onmessage` handler -- see
///   [`crate::js_api::worker_glue::generate_worker_bootstrap_js`] and
///   [`crate::js_api::preemptible_worker::PreemptibleSolver`].
#[wasm_bindgen]
pub struct WorkerHandler {
    /// Solver context
    ctx: oxiz_solver::Context,
    /// Current task ID
    current_task: Option<String>,
    /// Statistics
    tasks_processed: usize,
    /// Cooperative cancellation flag checked between operations inside
    /// [`WorkerHandler::handle_solve`] -- see [`CancellationToken`]'s
    /// docs for exactly what this can and cannot preempt.
    cancellation: CancellationToken,
}

#[wasm_bindgen]
impl WorkerHandler {
    /// Create a new worker handler
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        Self {
            ctx: oxiz_solver::Context::new(),
            current_task: None,
            tasks_processed: 0,
            cancellation: CancellationToken::new(),
        }
    }

    /// Attach a shared cancellation buffer received from the main thread
    /// (typically via `data.cancellationBuffer` in an `"init"` message --
    /// see [`WorkerHandler::handle_message`]), replacing whatever
    /// cancellation token this handler was using before.
    #[wasm_bindgen(js_name = attachCancellationBuffer)]
    pub fn attach_cancellation_buffer(&mut self, buffer: js_sys::SharedArrayBuffer) {
        self.cancellation = CancellationToken::from_buffer(buffer);
    }

    /// Request cooperative cancellation of the in-progress (or next)
    /// `WorkerHandler::handle_solve` call. See [`CancellationToken`]'s
    /// docs: this is observed only between operations, not inside a
    /// single `check_sat` call.
    pub fn cancel(&self) {
        self.cancellation.cancel();
    }

    /// Whether cooperative cancellation has been requested.
    #[wasm_bindgen(js_name = isCancelled)]
    pub fn is_cancelled(&self) -> bool {
        self.cancellation.is_cancelled()
    }

    /// Clear a pending cooperative cancellation request.
    #[wasm_bindgen(js_name = resetCancellation)]
    pub fn reset_cancellation(&self) {
        self.cancellation.reset();
    }

    /// Message-passing entry point for use as a real `Worker`'s
    /// `onmessage` handler (see the type-level docs for why this differs
    /// from [`WorkerHandler::handle_task`]).
    ///
    /// Accepts a plain JS object shaped as
    /// `{ id, type: "init" | "solve" | "cancel" | "shutdown", data?: {...} }`
    /// and returns a plain result object shaped as
    /// `{ id, type: "result" | "error", status?, ... }`, always echoing
    /// back the request `id` so the caller can match responses to
    /// in-flight requests.
    ///
    /// * `"init"` -- optionally attaches `data.cancellationBuffer` (a
    ///   `SharedArrayBuffer`) via [`WorkerHandler::attach_cancellation_buffer`].
    /// * `"solve"` -- resets cancellation, then behaves like
    ///   `WorkerHandler::handle_solve` with `data` as the payload
    ///   (`{ logic?, declarations?, assertions? }`), checking
    ///   cancellation between each declaration/assertion and again
    ///   immediately before `check_sat`.
    /// * `"cancel"` -- cooperative only (see module docs): this message
    ///   is only dequeued once the worker's current synchronous JS turn
    ///   finishes, so it cannot interrupt an in-progress `solve`. Prefer
    ///   `data.cancellationBuffer` (checked without needing a message
    ///   dispatch) or `Worker.terminate()` from the main thread.
    /// * `"shutdown"` -- acknowledged only; the caller is responsible for
    ///   actually terminating the worker.
    #[wasm_bindgen(js_name = handleMessage)]
    pub fn handle_message(&mut self, msg: JsValue) -> JsValue {
        let id = js_sys::Reflect::get(&msg, &"id".into()).unwrap_or(JsValue::UNDEFINED);
        let msg_type = js_sys::Reflect::get(&msg, &"type".into())
            .ok()
            .and_then(|v| v.as_string())
            .unwrap_or_default();
        let data = js_sys::Reflect::get(&msg, &"data".into()).unwrap_or(JsValue::UNDEFINED);

        let response = match msg_type.as_str() {
            "init" => {
                if let Ok(buf) = js_sys::Reflect::get(&data, &"cancellationBuffer".into())
                    && let Some(buf) = buf.dyn_ref::<js_sys::SharedArrayBuffer>()
                {
                    self.attach_cancellation_buffer(buf.clone());
                }
                let result = js_sys::Object::new();
                let _ = js_sys::Reflect::set(&result, &"type".into(), &"result".into());
                let _ = js_sys::Reflect::set(&result, &"status".into(), &"ready".into());
                result.into()
            }
            "cancel" => {
                self.cancellation.cancel();
                let result = js_sys::Object::new();
                let _ = js_sys::Reflect::set(&result, &"type".into(), &"result".into());
                let _ = js_sys::Reflect::set(&result, &"status".into(), &"cancel_requested".into());
                result.into()
            }
            "shutdown" => {
                let result = js_sys::Object::new();
                let _ = js_sys::Reflect::set(&result, &"type".into(), &"result".into());
                let _ = js_sys::Reflect::set(&result, &"status".into(), &"shutdown".into());
                result.into()
            }
            "solve" => {
                self.cancellation.reset();
                let solve_result = self.handle_solve(data);
                let _ = js_sys::Reflect::set(&solve_result, &"type".into(), &"result".into());
                solve_result
            }
            other => {
                let result = js_sys::Object::new();
                let _ = js_sys::Reflect::set(&result, &"type".into(), &"error".into());
                let _ = js_sys::Reflect::set(
                    &result,
                    &"error".into(),
                    &format!("Unknown message type: {other}").into(),
                );
                result.into()
            }
        };

        let _ = js_sys::Reflect::set(&response, &"id".into(), &id);
        response
    }

    /// Handle a task
    #[wasm_bindgen(js_name = handleTask)]
    pub fn handle_task(&mut self, task: WorkerTask) -> JsValue {
        self.current_task = Some(task.get_id());

        let start_time = web_sys::window()
            .and_then(|w| w.performance())
            .map(|p| p.now())
            .unwrap_or(0.0);

        // Process task based on type
        let result = match task.get_type().as_str() {
            "solve" => self.handle_solve(task.get_data()),
            "check-sat" => self.handle_check_sat(task.get_data()),
            "get-model" => self.handle_get_model(),
            _ => {
                let error = js_sys::Object::new();
                let _ = js_sys::Reflect::set(&error, &"error".into(), &"Unknown task type".into());
                error.into()
            }
        };

        let end_time = web_sys::window()
            .and_then(|w| w.performance())
            .map(|p| p.now())
            .unwrap_or(start_time);

        self.tasks_processed += 1;
        self.current_task = None;

        // Add timing info
        let _ = js_sys::Reflect::set(&result, &"time_ms".into(), &(end_time - start_time).into());
        let _ = js_sys::Reflect::set(&result, &"task_id".into(), &task.get_id().into());

        result
    }

    /// Get tasks processed count
    #[wasm_bindgen(js_name = tasksProcessed)]
    pub fn tasks_processed(&self) -> usize {
        self.tasks_processed
    }

    // Helper methods

    ///
    /// # Cooperative cancellation
    ///
    /// [`WorkerHandler::cancellation`] is checked before each declaration,
    /// before each assertion, and immediately before `check_sat` is
    /// called -- so a cancellation requested before (or between) those
    /// steps stops the batch promptly with `{ status: "cancelled" }`
    /// instead of running to completion. It is deliberately **not**
    /// checked inside `check_sat` itself: `oxiz_solver::Context::
    /// check_sat` has no cancellation hook to poll (adding one is out of
    /// scope for `oxiz-wasm`), so once a `check_sat` call starts it always
    /// runs to completion. See [`CancellationToken`]'s docs.
    fn handle_solve(&mut self, data: JsValue) -> JsValue {
        let result = js_sys::Object::new();

        if self.cancellation.is_cancelled() {
            return Self::solve_cancelled(&result);
        }

        // Extract logic from data
        if let Ok(logic) = js_sys::Reflect::get(&data, &"logic".into())
            && let Some(logic_str) = logic.as_string()
        {
            let _ = self.ctx.set_logic(&logic_str);
        }

        // Optional declarations: an array of `{name, sort}` objects,
        // processed before assertions so assertions referencing them
        // don't spuriously fail to parse as "undeclared symbol".
        if let Ok(declarations) = js_sys::Reflect::get(&data, &"declarations".into())
            && let Some(arr) = declarations.dyn_ref::<js_sys::Array>()
        {
            for decl in arr.iter() {
                if self.cancellation.is_cancelled() {
                    return Self::solve_cancelled(&result);
                }
                let name = js_sys::Reflect::get(&decl, &"name".into())
                    .ok()
                    .and_then(|v| v.as_string());
                let sort = js_sys::Reflect::get(&decl, &"sort".into())
                    .ok()
                    .and_then(|v| v.as_string());
                match (name, sort) {
                    (Some(name), Some(sort)) => {
                        let script = format!("(declare-const {} {})", name, sort);
                        if let Err(e) = self.ctx.execute_script(&script) {
                            return Self::solve_error(
                                &result,
                                format!("Failed to declare '{}': {}", name, e),
                            );
                        }
                    }
                    _ => {
                        return Self::solve_error(
                            &result,
                            "Invalid declaration entry: expected {name, sort}".to_string(),
                        );
                    }
                }
            }
        }

        // Execute assertions. Any parse/type error must abort the task
        // with an explicit error result instead of being silently
        // dropped -- proceeding to check-sat on a partial/emptied
        // assertion set could answer "sat" for a problem the caller
        // intended to be constrained (or unsat).
        if let Ok(assertions) = js_sys::Reflect::get(&data, &"assertions".into())
            && let Some(arr) = assertions.dyn_ref::<js_sys::Array>()
        {
            for assertion in arr.iter() {
                if self.cancellation.is_cancelled() {
                    return Self::solve_cancelled(&result);
                }
                match assertion.as_string() {
                    Some(formula) => {
                        let script = format!("(assert {})", formula);
                        if let Err(e) = self.ctx.execute_script(&script) {
                            return Self::solve_error(
                                &result,
                                format!("Failed to assert '{}': {}", formula, e),
                            );
                        }
                    }
                    None => {
                        return Self::solve_error(
                            &result,
                            "Assertion entries must be strings".to_string(),
                        );
                    }
                }
            }
        }

        if self.cancellation.is_cancelled() {
            return Self::solve_cancelled(&result);
        }

        // Check satisfiability. NOTE: once this call starts, cancellation
        // can no longer stop it early -- see the cooperative-cancellation
        // doc comment above.
        let sat_result = self.ctx.check_sat();
        let status = match sat_result {
            oxiz_solver::SolverResult::Sat => "sat",
            oxiz_solver::SolverResult::Unsat => "unsat",
            oxiz_solver::SolverResult::Unknown => "unknown",
        };

        let _ = js_sys::Reflect::set(&result, &"status".into(), &status.into());

        result.into()
    }

    /// Build an error result object: `{ status: "error", error: message }`.
    fn solve_error(result: &js_sys::Object, message: String) -> JsValue {
        let _ = js_sys::Reflect::set(result, &"status".into(), &"error".into());
        let _ = js_sys::Reflect::set(result, &"error".into(), &message.into());
        result.clone().into()
    }

    /// Build a `{ status: "cancelled" }` result object -- distinct from
    /// [`WorkerHandler::solve_error`] so callers can tell "the caller
    /// asked us to stop" apart from "the input was rejected".
    fn solve_cancelled(result: &js_sys::Object) -> JsValue {
        let _ = js_sys::Reflect::set(result, &"status".into(), &"cancelled".into());
        result.clone().into()
    }

    fn handle_check_sat(&mut self, _data: JsValue) -> JsValue {
        let result = js_sys::Object::new();
        let sat_result = self.ctx.check_sat();
        let status = match sat_result {
            oxiz_solver::SolverResult::Sat => "sat",
            oxiz_solver::SolverResult::Unsat => "unsat",
            oxiz_solver::SolverResult::Unknown => "unknown",
        };
        let _ = js_sys::Reflect::set(&result, &"status".into(), &status.into());
        result.into()
    }

    fn handle_get_model(&self) -> JsValue {
        let result = js_sys::Object::new();
        let model = self.ctx.get_model();
        let model_str = match model {
            Some(entries) => entries
                .iter()
                .map(|(name, sort, value)| format!("({} {} {})", name, sort, value))
                .collect::<Vec<_>>()
                .join("\n"),
            None => String::new(),
        };
        let _ = js_sys::Reflect::set(&result, &"model".into(), &model_str.into());
        result.into()
    }
}

impl Default for WorkerHandler {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_worker_message_type() {
        assert_eq!(WorkerMessageType::Init.name(), "init");
        assert_eq!(
            WorkerMessageType::from_str("execute"),
            Some(WorkerMessageType::Execute)
        );
        assert_eq!(WorkerMessageType::from_str("invalid"), None);
    }

    #[test]
    fn test_worker_task() {
        let task = WorkerTask::new("task1".to_string(), "solve".to_string(), JsValue::NULL);

        assert_eq!(task.get_id(), "task1");
        assert_eq!(task.get_type(), "solve");
    }

    #[test]
    #[cfg(target_arch = "wasm32")]
    fn test_worker_pool() {
        let pool = WorkerPool::new(4);
        pool.init();

        assert_eq!(pool.worker_count, 4);
        assert_eq!(pool.queue_length(), 0);
    }

    #[test]
    #[cfg(target_arch = "wasm32")]
    fn test_worker_pool_submit() {
        let pool = WorkerPool::new(2);
        pool.init();

        let task = WorkerTask::new("task1".to_string(), "solve".to_string(), JsValue::NULL);

        pool.submit(task);
        assert_eq!(pool.queue_length(), 1);
    }

    #[test]
    fn test_worker_handler() {
        let handler = WorkerHandler::new();
        assert_eq!(handler.tasks_processed(), 0);
    }

    // `WorkerHandler`'s cancellation plumbing delegates to a local-mode
    // `CancellationToken` (pure `Rc<Cell<bool>>`, no JS calls) unless/until
    // `attach_cancellation_buffer` is used, so this can run natively --
    // unlike `handle_message`/`handle_solve` below, which build
    // `js_sys::Object`/`JsValue` and therefore require a wasm32 JS host
    // (see the empirical note in `async_utils`'s tests).
    #[test]
    fn test_worker_handler_cancellation_plumbing() {
        let handler = WorkerHandler::new();
        assert!(!handler.is_cancelled());

        handler.cancel();
        assert!(handler.is_cancelled());

        handler.reset_cancellation();
        assert!(!handler.is_cancelled());
    }

    #[test]
    #[cfg(target_arch = "wasm32")]
    fn test_handle_message_init_ready() {
        let mut handler = WorkerHandler::new();
        let msg = js_sys::Object::new();
        let _ = js_sys::Reflect::set(&msg, &"id".into(), &1.into());
        let _ = js_sys::Reflect::set(&msg, &"type".into(), &"init".into());

        let response = handler.handle_message(msg.into());
        let ty = js_sys::Reflect::get(&response, &"type".into())
            .ok()
            .and_then(|v| v.as_string());
        let status = js_sys::Reflect::get(&response, &"status".into())
            .ok()
            .and_then(|v| v.as_string());
        let id = js_sys::Reflect::get(&response, &"id".into())
            .ok()
            .and_then(|v| v.as_f64());
        assert_eq!(ty.as_deref(), Some("result"));
        assert_eq!(status.as_deref(), Some("ready"));
        assert_eq!(id, Some(1.0));
    }

    #[test]
    #[cfg(target_arch = "wasm32")]
    fn test_handle_message_unknown_type_is_error() {
        let mut handler = WorkerHandler::new();
        let msg = js_sys::Object::new();
        let _ = js_sys::Reflect::set(&msg, &"id".into(), &7.into());
        let _ = js_sys::Reflect::set(&msg, &"type".into(), &"bogus".into());

        let response = handler.handle_message(msg.into());
        let ty = js_sys::Reflect::get(&response, &"type".into())
            .ok()
            .and_then(|v| v.as_string());
        assert_eq!(ty.as_deref(), Some("error"));
    }

    #[test]
    #[cfg(target_arch = "wasm32")]
    fn test_handle_message_solve_end_to_end() {
        let mut handler = WorkerHandler::new();
        let msg = js_sys::Object::new();
        let _ = js_sys::Reflect::set(&msg, &"id".into(), &2.into());
        let _ = js_sys::Reflect::set(&msg, &"type".into(), &"solve".into());

        let data = js_sys::Object::new();
        let _ = js_sys::Reflect::set(&data, &"logic".into(), &"QF_LIA".into());
        let decls = js_sys::Array::new();
        let decl = js_sys::Object::new();
        let _ = js_sys::Reflect::set(&decl, &"name".into(), &"x".into());
        let _ = js_sys::Reflect::set(&decl, &"sort".into(), &"Int".into());
        decls.push(&decl);
        let _ = js_sys::Reflect::set(&data, &"declarations".into(), &decls);
        let assertions = js_sys::Array::new();
        assertions.push(&"(> x 0)".into());
        let _ = js_sys::Reflect::set(&data, &"assertions".into(), &assertions);
        let _ = js_sys::Reflect::set(&msg, &"data".into(), &data);

        let response = handler.handle_message(msg.into());
        let status = js_sys::Reflect::get(&response, &"status".into())
            .ok()
            .and_then(|v| v.as_string());
        assert_eq!(status.as_deref(), Some("sat"));
    }

    #[test]
    #[cfg(target_arch = "wasm32")]
    fn test_handle_solve_returns_cancelled_when_pre_cancelled() {
        // `handle_solve`'s very first check must short-circuit with
        // `status: "cancelled"` (not run any declarations/assertions/
        // check_sat) when the cooperative token is already cancelled.
        // Called directly (bypassing `handle_message`, which resets
        // cancellation at the start of its "solve" arm) to isolate this
        // specific guarantee.
        let mut handler = WorkerHandler::new();
        handler.cancel();

        let data = js_sys::Object::new();
        let _ = js_sys::Reflect::set(&data, &"logic".into(), &"QF_LIA".into());

        let result = handler.handle_solve(data.into());
        let status = js_sys::Reflect::get(&result, &"status".into())
            .ok()
            .and_then(|v| v.as_string());
        assert_eq!(status.as_deref(), Some("cancelled"));
    }

    #[test]
    #[cfg(target_arch = "wasm32")]
    fn test_handle_message_solve_resets_stale_cancellation() {
        // A cancellation left over from a *previous* solve must not leak
        // into the next one dispatched via `handle_message` -- otherwise
        // every solve after the first cancelled one would spuriously
        // report "cancelled" forever.
        let mut handler = WorkerHandler::new();
        handler.cancel();
        assert!(handler.is_cancelled());

        let msg = js_sys::Object::new();
        let _ = js_sys::Reflect::set(&msg, &"id".into(), &4.into());
        let _ = js_sys::Reflect::set(&msg, &"type".into(), &"solve".into());
        let data = js_sys::Object::new();
        let _ = js_sys::Reflect::set(&data, &"logic".into(), &"QF_LIA".into());
        let _ = js_sys::Reflect::set(&msg, &"data".into(), &data);

        let response = handler.handle_message(msg.into());
        let status = js_sys::Reflect::get(&response, &"status".into())
            .ok()
            .and_then(|v| v.as_string());
        assert_ne!(status.as_deref(), Some("cancelled"));
        assert!(!handler.is_cancelled());
    }
}
