//! Distributed PDR for solving large CHC systems across multiple workers.
//!
//! This module provides the message-passing / shared-state *infrastructure*
//! (coordinator, workers, work queue, frame synchronization) for distributing
//! a Constrained Horn Clause solve across cooperating workers.
//!
//! ## Current status: documented single-process fallback
//!
//! A genuinely distributed PDR engine needs the CHC system and term manager to
//! be shared *mutably* across worker threads. The current ownership model —
//! [`Spacer`] borrows `&mut TermManager`, and [`ChcSystem`] is not `Clone`
//! (it holds atomic ID counters) — does not support that yet. Rather than
//! fabricate block/sleep results (which would make the exported API silently
//! unsound), [`DistributedCoordinator::solve`] and [`Worker::run`] **delegate
//! to the sound, sequential [`Spacer`] engine** and return its exact result.
//! The scaffolding below (queue, messages, shared frames) is retained for the
//! future multi-worker implementation.
//!
//! ## Architecture (target design)
//!
//! - **Coordinator**: Manages work distribution and result aggregation
//! - **Workers**: Process proof obligations and learn lemmas independently
//! - **Shared State**: Frame lemmas are synchronized across workers
//! - **Communication**: Message passing for work items and learned lemmas
//!
//! Reference: Distributed PDR algorithms from literature

use crate::chc::{ChcSystem, PredId};
use crate::frames::{FrameManager, LemmaId};
use crate::pdr::{Spacer, SpacerConfig, SpacerError, SpacerResult, SpacerStats};
use crate::pob::{Pob, PobId};
use oxiz_core::{TermId, TermManager};
use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use thiserror::Error;

/// Errors that can occur in distributed solving
#[derive(Error, Debug)]
pub enum DistributedError {
    /// Worker error
    #[error("worker {0} error: {1}")]
    WorkerError(usize, String),
    /// Communication error
    #[error("communication error: {0}")]
    Communication(String),
    /// Coordination error
    #[error("coordination error: {0}")]
    Coordination(String),
    /// Spacer error from underlying solver
    #[error("spacer error: {0}")]
    Spacer(#[from] SpacerError),
    /// Timeout
    #[error("timeout after {0:?}")]
    Timeout(Duration),
}

/// Configuration for distributed solving
#[derive(Debug, Clone)]
pub struct DistributedConfig {
    /// Number of worker threads
    pub num_workers: usize,
    /// Base configuration for each worker
    pub worker_config: SpacerConfig,
    /// Synchronization interval (ms)
    pub sync_interval_ms: u64,
    /// Timeout for distributed solving
    pub timeout: Option<Duration>,
    /// Enable work stealing between workers
    pub enable_work_stealing: bool,
}

impl Default for DistributedConfig {
    fn default() -> Self {
        Self {
            num_workers: num_cpus::get(),
            worker_config: SpacerConfig::default(),
            sync_interval_ms: 100,
            timeout: None,
            enable_work_stealing: true,
        }
    }
}

/// Message types for worker communication
#[derive(Debug, Clone)]
pub enum WorkerMessage {
    /// Work item (POB) to process
    Work(WorkItem),
    /// Lemma learned by a worker
    LemmaLearned {
        worker_id: usize,
        pred: PredId,
        lemma: TermId,
        level: u32,
    },
    /// Frame created
    FrameCreated { level: u32 },
    /// Result from processing a POB
    WorkResult {
        worker_id: usize,
        pob_id: PobId,
        blocked: bool,
        lemma: Option<LemmaId>,
    },
    /// Counterexample found
    Counterexample { worker_id: usize },
    /// Invariant found (fixpoint detected)
    Invariant { worker_id: usize, level: u32 },
    /// Worker requesting work (for work stealing)
    RequestWork { worker_id: usize },
    /// Shutdown signal
    Shutdown,
}

/// Work item for distributed processing
#[derive(Debug, Clone)]
pub struct WorkItem {
    /// POB identifier
    pub pob_id: PobId,
    /// The POB to process
    pub pob: Pob,
    /// Priority (higher = more urgent)
    pub priority: i32,
}

/// Shared state between workers
pub struct SharedState {
    /// Frame manager (synchronized across workers)
    frames: Mutex<FrameManager>,
    /// Work queue
    work_queue: Mutex<VecDeque<WorkItem>>,
    /// Result
    result: Mutex<Option<SpacerResult>>,
    /// Combined statistics
    stats: Mutex<DistributedStats>,
    /// Message channels
    messages: Mutex<VecDeque<WorkerMessage>>,
}

impl SharedState {
    /// Create new shared state
    pub fn new() -> Self {
        Self {
            frames: Mutex::new(FrameManager::new()),
            work_queue: Mutex::new(VecDeque::new()),
            result: Mutex::new(None),
            stats: Mutex::new(DistributedStats::default()),
            messages: Mutex::new(VecDeque::new()),
        }
    }

    /// Add work item to queue
    pub fn enqueue_work(&self, item: WorkItem) {
        let mut queue = self.work_queue.lock().expect("lock should not be poisoned");
        // Insert based on priority (higher priority first)
        let pos = queue
            .iter()
            .position(|w| w.priority < item.priority)
            .unwrap_or(queue.len());
        queue.insert(pos, item);
    }

    /// Dequeue work item
    pub fn dequeue_work(&self) -> Option<WorkItem> {
        self.work_queue
            .lock()
            .expect("lock should not be poisoned")
            .pop_front()
    }

    /// Get number of pending work items
    pub fn work_queue_size(&self) -> usize {
        self.work_queue
            .lock()
            .expect("lock should not be poisoned")
            .len()
    }

    /// Send message to workers
    pub fn send_message(&self, msg: WorkerMessage) {
        self.messages
            .lock()
            .expect("lock should not be poisoned")
            .push_back(msg);
    }

    /// Receive message
    pub fn receive_message(&self) -> Option<WorkerMessage> {
        self.messages
            .lock()
            .expect("lock should not be poisoned")
            .pop_front()
    }

    /// Set result
    pub fn set_result(&self, result: SpacerResult) {
        *self.result.lock().expect("lock should not be poisoned") = Some(result);
    }

    /// Get result
    pub fn get_result(&self) -> Option<SpacerResult> {
        self.result
            .lock()
            .expect("lock should not be poisoned")
            .clone()
    }

    /// Add lemma to frames
    pub fn add_lemma(&self, pred: PredId, formula: TermId, level: u32) -> LemmaId {
        self.frames
            .lock()
            .expect("lock should not be poisoned")
            .add_lemma(pred, formula, level)
    }

    /// Get frame manager (locked)
    pub fn with_frames<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut FrameManager) -> R,
    {
        let mut frames = self.frames.lock().expect("lock should not be poisoned");
        f(&mut frames)
    }

    /// Update statistics
    pub fn update_stats<F>(&self, f: F)
    where
        F: FnOnce(&mut DistributedStats),
    {
        let mut stats = self.stats.lock().expect("lock should not be poisoned");
        f(&mut stats);
    }

    /// Get statistics
    pub fn get_stats(&self) -> DistributedStats {
        self.stats
            .lock()
            .expect("lock should not be poisoned")
            .clone()
    }
}

impl Default for SharedState {
    fn default() -> Self {
        Self::new()
    }
}

/// Statistics for distributed solving
#[derive(Debug, Clone, Default)]
pub struct DistributedStats {
    /// Per-worker statistics
    pub worker_stats: HashMap<usize, SpacerStats>,
    /// Total work items processed
    pub total_work_items: u64,
    /// Total lemmas learned
    pub total_lemmas: u64,
    /// Work stealing events
    pub work_stealing_events: u64,
    /// Synchronization events
    pub sync_events: u64,
    /// Communication overhead (messages sent)
    pub messages_sent: u64,
}

impl DistributedStats {
    /// Create new distributed statistics
    pub fn new() -> Self {
        Self::default()
    }

    /// Aggregate statistics from all workers
    pub fn aggregate(&self) -> SpacerStats {
        let mut total = SpacerStats::default();
        for stats in self.worker_stats.values() {
            total.num_frames = total.num_frames.max(stats.num_frames);
            total.num_lemmas = total.num_lemmas.saturating_add(stats.num_lemmas);
            total.num_inductive = total.num_inductive.saturating_add(stats.num_inductive);
            total.num_pobs = total.num_pobs.saturating_add(stats.num_pobs);
            total.num_blocked = total.num_blocked.saturating_add(stats.num_blocked);
            total.num_smt_queries = total.num_smt_queries.saturating_add(stats.num_smt_queries);
            total.num_propagations = total
                .num_propagations
                .saturating_add(stats.num_propagations);
            total.num_subsumed = total.num_subsumed.saturating_add(stats.num_subsumed);
            total.num_mic_attempts = total
                .num_mic_attempts
                .saturating_add(stats.num_mic_attempts);
            total.num_ctg_strengthenings = total
                .num_ctg_strengthenings
                .saturating_add(stats.num_ctg_strengthenings);
        }
        total
    }
}

/// Worker thread for distributed solving
pub struct Worker {
    /// Worker ID
    id: usize,
    /// Shared state
    shared: Arc<SharedState>,
    /// Local statistics
    stats: SpacerStats,
}

impl Worker {
    /// Create a new worker
    pub fn new(id: usize, shared: Arc<SharedState>) -> Self {
        Self {
            id,
            shared,
            stats: SpacerStats::default(),
        }
    }

    /// Run the worker.
    ///
    /// Single-process fallback (see the module-level docs): rather than
    /// fabricate proof-obligation outcomes, the worker runs the sound,
    /// sequential [`Spacer`] engine on the shared system and publishes the
    /// **real** result plus its solver statistics. Genuine multi-worker POB
    /// distribution over the shared queue is future work.
    pub fn run(
        &mut self,
        terms: &mut TermManager,
        system: &ChcSystem,
        config: &SpacerConfig,
    ) -> Result<(), DistributedError> {
        // If a peer already found the answer, honor the shutdown / result and
        // do not redundantly re-solve.
        if self.shared.get_result().is_some() {
            return Ok(());
        }
        if let Some(WorkerMessage::Shutdown) = self.shared.receive_message() {
            return Ok(());
        }

        let mut spacer = Spacer::with_config(terms, system, config.clone());
        let result = spacer.solve()?;
        self.stats = spacer.stats().clone();

        // Publish the real result and this worker's statistics.
        self.shared.set_result(result);
        let worker_id = self.id;
        let stats = self.stats.clone();
        let num_pobs = u64::from(self.stats.num_pobs);
        self.shared.update_stats(move |s| {
            s.worker_stats.insert(worker_id, stats);
            s.total_work_items = s.total_work_items.saturating_add(num_pobs);
        });

        Ok(())
    }
}

/// Coordinator for distributed solving
#[allow(dead_code)]
pub struct DistributedCoordinator<'a> {
    /// Term manager
    terms: &'a mut TermManager,
    /// CHC system
    system: &'a ChcSystem,
    /// Configuration
    config: DistributedConfig,
    /// Shared state
    shared: Arc<SharedState>,
    /// Start time
    start_time: Instant,
}

impl<'a> DistributedCoordinator<'a> {
    /// Create a new distributed coordinator
    pub fn new(
        terms: &'a mut TermManager,
        system: &'a ChcSystem,
        config: DistributedConfig,
    ) -> Self {
        Self {
            terms,
            system,
            config,
            shared: Arc::new(SharedState::new()),
            start_time: Instant::now(),
        }
    }

    /// Solve the CHC system.
    ///
    /// **Single-process fallback.** As documented at the module level, a
    /// genuinely distributed PDR engine is not yet implemented (it needs the
    /// term manager and CHC system to be shared mutably across threads, which
    /// the current ownership model forbids). Instead of returning a fabricated
    /// answer derived from sleep-based "work", this delegates to the sound,
    /// sequential [`Spacer`] engine and returns its exact result — so the
    /// exported API is always honest: `Safe`/`Unsafe` when the sequential
    /// engine decides, `Unknown` when it cannot (including on timeout).
    pub fn solve(&mut self) -> Result<SpacerResult, DistributedError> {
        // Honor an explicit distributed timeout by bounding the sequential
        // engine's work via its resource limits is not directly expressible,
        // so we run the sound engine and surface its verdict.  The engine
        // itself returns `Unknown` rather than an unsound answer when it hits
        // its own limits.
        let config = self.config.worker_config.clone();

        let result = {
            let mut spacer = Spacer::with_config(self.terms, self.system, config);
            spacer.solve()?
        };

        self.shared.set_result(result.clone());
        self.shared.update_stats(|stats| {
            stats.total_work_items = stats.total_work_items.saturating_add(1);
        });

        Ok(result)
    }

    /// Check if timeout exceeded
    #[allow(dead_code)]
    fn is_timeout(&self) -> bool {
        if let Some(timeout) = self.config.timeout {
            self.start_time.elapsed() >= timeout
        } else {
            false
        }
    }
}

/// Dummy num_cpus implementation (simplified)
mod num_cpus {
    pub fn get() -> usize {
        // Default to 4 workers if we can't detect
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shared_state_work_queue() {
        let state = SharedState::new();

        // Enqueue work items with different priorities
        state.enqueue_work(WorkItem {
            pob_id: PobId(0),
            pob: Pob::new(PobId(0), PredId(0), TermId(0), 0, 0),
            priority: 10,
        });

        state.enqueue_work(WorkItem {
            pob_id: PobId(1),
            pob: Pob::new(PobId(1), PredId(0), TermId(1), 0, 0),
            priority: 20, // Higher priority
        });

        // Should dequeue higher priority first
        let work = state.dequeue_work().expect("test operation should succeed");
        assert_eq!(work.pob_id, PobId(1));
        assert_eq!(work.priority, 20);
    }

    #[test]
    fn test_distributed_stats_aggregate() {
        let mut stats = DistributedStats::new();

        stats.worker_stats.insert(
            0,
            SpacerStats {
                num_frames: 5,
                num_lemmas: 10,
                num_pobs: 20,
                ..Default::default()
            },
        );

        stats.worker_stats.insert(
            1,
            SpacerStats {
                num_frames: 7, // Max should be 7
                num_lemmas: 15,
                num_pobs: 25,
                ..Default::default()
            },
        );

        let aggregated = stats.aggregate();
        assert_eq!(aggregated.num_frames, 7); // Max of 5 and 7
        assert_eq!(aggregated.num_lemmas, 25); // Sum: 10 + 15
        assert_eq!(aggregated.num_pobs, 45); // Sum: 20 + 25
    }
}
