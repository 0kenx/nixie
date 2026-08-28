//! Parallel frame solving for Spacer.
//!
//! This module provides infrastructure for parallel processing of frames
//! and proof obligations, improving performance on multi-core systems.
//!
//! Reference: Z3's parallel PDR and portfolio approaches

use crate::chc::{ChcSystem, PredId};
use crate::frames::{FrameManager, LemmaId};
use crate::pob::PobId;
use crate::smt::{SmtSolver, build_frame_formula};
use oxiz_core::TermManager;
use oxiz_time::Duration;
use std::sync::{Arc, Mutex};
use std::thread;
use thiserror::Error;
use tracing::{debug, trace};

/// Errors that can occur in parallel solving
#[derive(Error, Debug)]
pub enum ParallelError {
    /// Thread pool error
    #[error("thread pool error: {0}")]
    ThreadPool(String),
    /// Synchronization error
    #[error("synchronization error: {0}")]
    Sync(String),
    /// Worker timeout
    #[error("worker timeout")]
    Timeout,
}

/// Configuration for parallel solving
#[derive(Debug, Clone)]
pub struct ParallelConfig {
    /// Number of worker threads (0 = auto-detect)
    pub num_workers: usize,
    /// Enable parallel frame propagation
    pub parallel_propagation: bool,
    /// Enable parallel POB blocking
    pub parallel_blocking: bool,
    /// Maximum queue size per worker
    pub max_queue_size: usize,
}

impl Default for ParallelConfig {
    fn default() -> Self {
        Self {
            num_workers: 0, // Auto-detect
            parallel_propagation: true,
            parallel_blocking: true,
            max_queue_size: 1000,
        }
    }
}

/// Work item for parallel processing
#[derive(Debug, Clone)]
pub enum WorkItem {
    /// Propagate a lemma to higher frames
    PropagateLemma {
        /// The predicate the lemma belongs to (`LemmaId`s are only unique
        /// *within* a single predicate's frame sequence, so the predicate
        /// must be known to look the lemma up at all).
        pred: PredId,
        /// Lemma to propagate
        lemma_id: LemmaId,
        /// Starting frame level
        from_level: u32,
    },
    /// Block a proof obligation
    BlockPob {
        /// POB to block
        pob_id: PobId,
    },
    /// Check subsumption between lemmas
    CheckSubsumption {
        /// First lemma
        lemma_a: LemmaId,
        /// Second lemma
        lemma_b: LemmaId,
    },
}

/// Result of processing a work item
#[derive(Debug, Clone)]
pub enum WorkResult {
    /// Lemma successfully propagated
    LemmaPropagated {
        /// Lemma ID
        lemma_id: LemmaId,
        /// New frame level
        new_level: u32,
    },
    /// POB successfully blocked
    PobBlocked {
        /// POB ID
        pob_id: PobId,
        /// Blocking lemma
        lemma_id: LemmaId,
    },
    /// Subsumption check result
    Subsumed {
        /// The subsumed lemma (can be removed)
        subsumed: LemmaId,
        /// The subsuming lemma
        subsuming: LemmaId,
    },
    /// The check ran successfully but the lemma is not (yet) inductive at
    /// the target level, so it was not propagated. This is a normal,
    /// expected outcome -- distinct from [`WorkResult::Failed`], which
    /// signals the check itself could not be completed.
    NotInductive {
        /// Lemma ID
        lemma_id: LemmaId,
    },
    /// Work item failed
    Failed {
        /// Error message
        error: String,
    },
}

/// Parallel work queue
pub struct WorkQueue {
    /// Work items to process
    items: Arc<Mutex<Vec<WorkItem>>>,
    /// Results from workers
    results: Arc<Mutex<Vec<WorkResult>>>,
    /// Configuration
    config: ParallelConfig,
}

impl WorkQueue {
    /// Create a new work queue
    pub fn new(config: ParallelConfig) -> Self {
        Self {
            items: Arc::new(Mutex::new(Vec::new())),
            results: Arc::new(Mutex::new(Vec::new())),
            config,
        }
    }

    /// Add a work item to the queue
    pub fn enqueue(&self, item: WorkItem) -> Result<(), ParallelError> {
        let mut items = self
            .items
            .lock()
            .map_err(|e| ParallelError::Sync(e.to_string()))?;

        if items.len() >= self.config.max_queue_size {
            return Err(ParallelError::Sync("queue full".to_string()));
        }

        items.push(item);
        Ok(())
    }

    /// Dequeue a work item (returns None if queue is empty)
    pub fn dequeue(&self) -> Result<Option<WorkItem>, ParallelError> {
        let mut items = self
            .items
            .lock()
            .map_err(|e| ParallelError::Sync(e.to_string()))?;

        Ok(items.pop())
    }

    /// Add a result
    pub fn add_result(&self, result: WorkResult) -> Result<(), ParallelError> {
        let mut results = self
            .results
            .lock()
            .map_err(|e| ParallelError::Sync(e.to_string()))?;

        results.push(result);
        Ok(())
    }

    /// Get all results and clear the result queue
    pub fn drain_results(&self) -> Result<Vec<WorkResult>, ParallelError> {
        let mut results = self
            .results
            .lock()
            .map_err(|e| ParallelError::Sync(e.to_string()))?;

        Ok(std::mem::take(&mut *results))
    }

    /// Check if queue is empty
    pub fn is_empty(&self) -> bool {
        self.items
            .lock()
            .map(|items| items.is_empty())
            .unwrap_or(true)
    }

    /// Get queue size
    pub fn size(&self) -> usize {
        self.items.lock().map(|items| items.len()).unwrap_or(0)
    }
}

/// Parallel frame solver
pub struct ParallelFrameSolver {
    /// Configuration
    config: ParallelConfig,
    /// Work queue
    queue: WorkQueue,
    /// Number of active workers
    active_workers: Arc<Mutex<usize>>,
}

impl ParallelFrameSolver {
    /// Create a new parallel frame solver
    pub fn new(config: ParallelConfig) -> Self {
        let queue = WorkQueue::new(config.clone());
        Self {
            config,
            queue,
            active_workers: Arc::new(Mutex::new(0)),
        }
    }

    /// Get the number of worker threads to use
    fn num_workers(&self) -> usize {
        if self.config.num_workers > 0 {
            self.config.num_workers
        } else {
            // Auto-detect: use number of CPUs
            thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(4)
        }
    }

    /// Spawn worker threads
    pub fn spawn_workers<F>(
        &self,
        worker_fn: F,
    ) -> Result<Vec<thread::JoinHandle<()>>, ParallelError>
    where
        F: Fn(WorkItem) -> WorkResult + Send + Sync + 'static + Clone,
    {
        let num_workers = self.num_workers();
        let mut handles = Vec::new();

        debug!("Spawning {} worker threads", num_workers);

        for worker_id in 0..num_workers {
            let queue = self.queue.items.clone();
            let results = self.queue.results.clone();
            let active_workers = self.active_workers.clone();
            let worker_fn = worker_fn.clone();

            let handle = thread::spawn(move || {
                trace!("Worker {} started", worker_id);

                // Increment active worker count
                if let Ok(mut count) = active_workers.lock() {
                    *count += 1;
                }

                loop {
                    // Try to get work item
                    let work_item = {
                        let mut items = match queue.lock() {
                            Ok(items) => items,
                            Err(e) => {
                                debug!("Worker {} failed to lock queue: {}", worker_id, e);
                                break;
                            }
                        };
                        items.pop()
                    };

                    match work_item {
                        Some(item) => {
                            trace!("Worker {} processing item: {:?}", worker_id, item);
                            let result = worker_fn(item);

                            // Add result
                            if let Ok(mut res) = results.lock() {
                                res.push(result);
                            }
                        }
                        None => {
                            // No work available, sleep briefly
                            thread::sleep(Duration::from_millis(10));

                            // Check if we should exit
                            // In a real implementation, we'd have a shutdown signal
                            break;
                        }
                    }
                }

                // Decrement active worker count
                if let Ok(mut count) = active_workers.lock() {
                    *count -= 1;
                }

                trace!("Worker {} finished", worker_id);
            });

            handles.push(handle);
        }

        Ok(handles)
    }

    /// Process work items in parallel
    pub fn process_parallel<F>(
        &self,
        items: Vec<WorkItem>,
        worker_fn: F,
    ) -> Result<Vec<WorkResult>, ParallelError>
    where
        F: Fn(WorkItem) -> WorkResult + Send + Sync + 'static + Clone,
    {
        // Add items to queue
        for item in items {
            self.queue.enqueue(item)?;
        }

        // Spawn workers
        let handles = self.spawn_workers(worker_fn)?;

        // Wait for workers to complete
        for handle in handles {
            handle
                .join()
                .map_err(|_| ParallelError::ThreadPool("worker thread panicked".to_string()))?;
        }

        // Collect results
        self.queue.drain_results()
    }

    /// Get the work queue
    pub fn queue(&self) -> &WorkQueue {
        &self.queue
    }

    /// Get active worker count
    pub fn active_workers(&self) -> usize {
        self.active_workers.lock().map(|c| *c).unwrap_or(0)
    }
}

/// Lemma propagation helper.
///
/// Despite the name (kept for API stability), lemma propagation itself
/// runs sequentially -- see [`Self::propagate_lemmas`] for why -- so this
/// no longer holds a [`ParallelFrameSolver`]; `config` is retained for
/// any future work-item kind this type grows that genuinely can run on
/// the worker-thread pool.
pub struct ParallelPropagator {
    /// Configuration (currently unused by `propagate_lemmas` itself, kept
    /// for future parallel work-item kinds).
    #[allow(dead_code)]
    config: ParallelConfig,
}

impl ParallelPropagator {
    /// Create a new parallel propagator
    pub fn new(config: ParallelConfig) -> Self {
        Self { config }
    }

    /// Propagate lemmas, checking genuine inductiveness via
    /// [`SmtSolver::is_lemma_inductive`] for each one.
    ///
    /// This used to report every lemma as `LemmaPropagated` unconditionally
    /// (a placeholder that never actually checked whether the lemma held
    /// at the higher level), which is unsound: it would let a
    /// non-inductive lemma get bumped to a frame it does not actually
    /// hold at, corrupting frame invariants and potentially causing a
    /// false fixpoint declaration.
    ///
    /// Note on "parallel": genuine SMT-backed inductiveness checking
    /// needs mutable, sequential access to a single [`TermManager`] (term
    /// interning is not thread-safe here), so -- unlike
    /// [`ParallelFrameSolver::process_parallel`]'s generic worker-thread
    /// dispatch used elsewhere in this module -- these checks run
    /// sequentially on the caller's thread. Running them one at a time
    /// with a correct answer is preferable to a "parallel" facade that
    /// cannot actually check anything.
    pub fn propagate_lemmas(
        &self,
        terms: &mut TermManager,
        system: &ChcSystem,
        frames: &FrameManager,
        lemmas: Vec<(PredId, LemmaId, u32)>,
    ) -> Result<Vec<WorkResult>, ParallelError> {
        let mut results = Vec::with_capacity(lemmas.len());

        for (pred, lemma_id, from_level) in lemmas {
            let Some(lemma_formula) = frames
                .get(pred)
                .and_then(|pred_frames| pred_frames.get_lemma(lemma_id))
                .map(|lemma| lemma.formula)
            else {
                results.push(WorkResult::Failed {
                    error: format!("lemma {lemma_id:?} not found for predicate {pred:?}"),
                });
                continue;
            };

            let frame_formula = build_frame_formula(terms, frames, pred, from_level);
            let mut smt = SmtSolver::new(terms, system);
            match smt.is_lemma_inductive(pred, lemma_formula, from_level, frame_formula) {
                Ok(true) => results.push(WorkResult::LemmaPropagated {
                    lemma_id,
                    new_level: from_level + 1,
                }),
                Ok(false) => results.push(WorkResult::NotInductive { lemma_id }),
                Err(e) => results.push(WorkResult::Failed {
                    error: e.to_string(),
                }),
            }
        }

        Ok(results)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parallel_config() {
        let config = ParallelConfig::default();
        assert_eq!(config.num_workers, 0); // Auto-detect
        assert!(config.parallel_propagation);
    }

    #[test]
    fn test_work_queue() {
        let config = ParallelConfig::default();
        let queue = WorkQueue::new(config);

        let item = WorkItem::PropagateLemma {
            pred: PredId::new(0),
            lemma_id: LemmaId(0),
            from_level: 1,
        };

        assert!(queue.enqueue(item).is_ok());
        assert_eq!(queue.size(), 1);
        assert!(!queue.is_empty());

        let dequeued = queue.dequeue().expect("test operation should succeed");
        assert!(dequeued.is_some());
        assert!(queue.is_empty());
    }

    #[test]
    fn test_work_result() {
        let result = WorkResult::LemmaPropagated {
            lemma_id: LemmaId(0),
            new_level: 2,
        };

        match result {
            WorkResult::LemmaPropagated {
                lemma_id,
                new_level,
            } => {
                assert_eq!(lemma_id, LemmaId(0));
                assert_eq!(new_level, 2);
            }
            _ => panic!("unexpected result type"),
        }
    }

    #[test]
    fn test_parallel_solver_creation() {
        let config = ParallelConfig::default();
        let solver = ParallelFrameSolver::new(config);
        assert_eq!(solver.active_workers(), 0);
    }

    /// Regression test for the `sweep-backend-misc` triage sweep:
    /// `propagate_lemmas` used to report every lemma as
    /// `LemmaPropagated` unconditionally, without any inductiveness
    /// check. Set up a real CHC system with one genuinely inductive
    /// lemma (`true`, trivially preserved by any transition) and one
    /// genuinely non-inductive lemma (`x = 0`, violated after one step
    /// of `x' = x + 1`), and verify each gets the correct, distinct
    /// outcome.
    #[test]
    fn test_parallel_propagator() {
        use crate::chc::PredicateApp;
        use crate::smt::canon_cur_vars;
        use oxiz_core::TermManager;

        let mut terms = TermManager::new();
        let mut system = ChcSystem::new();
        let pred = system.declare_predicate("ParPropInv", [terms.sorts.int_sort]);

        let x = terms.mk_var("par_prop_x", terms.sorts.int_sort);
        let zero = terms.mk_int(0);
        let init_c = terms.mk_eq(x, zero);
        system.add_init_rule(
            [("par_prop_x".to_string(), terms.sorts.int_sort)],
            init_c,
            pred,
            [x],
        );

        let x_next = terms.mk_var("par_prop_x_next", terms.sorts.int_sort);
        let one = terms.mk_int(1);
        let x_plus_one = terms.mk_add([x, one]);
        let trans_c = terms.mk_eq(x_next, x_plus_one);
        system.add_transition_rule(
            [
                ("par_prop_x".to_string(), terms.sorts.int_sort),
                ("par_prop_x_next".to_string(), terms.sorts.int_sort),
            ],
            [PredicateApp::new(pred, [x])],
            trans_c,
            pred,
            [x_next],
        );

        let mut frames = FrameManager::new();

        // Genuinely inductive: `true` is trivially preserved by any
        // transition.
        let true_term = terms.mk_true();
        let inductive_id = frames.add_lemma(pred, true_term, 1);

        // Genuinely NOT inductive: `x = 0` does not survive `x' = x + 1`.
        let cur_vars = canon_cur_vars(&mut terms, &system, pred);
        let zero_again = terms.mk_int(0);
        let noninductive_lemma = terms.mk_eq(cur_vars[0], zero_again);
        let noninductive_id = frames.add_lemma(pred, noninductive_lemma, 1);

        let config = ParallelConfig {
            num_workers: 2,
            parallel_propagation: true,
            parallel_blocking: true,
            max_queue_size: 100,
        };
        let propagator = ParallelPropagator::new(config);

        let lemmas = vec![(pred, inductive_id, 1), (pred, noninductive_id, 1)];
        let results = propagator
            .propagate_lemmas(&mut terms, &system, &frames, lemmas)
            .expect("propagate_lemmas should not error");

        assert_eq!(results.len(), 2);
        assert!(
            matches!(
                results[0],
                WorkResult::LemmaPropagated { lemma_id, new_level }
                    if lemma_id == inductive_id && new_level == 2
            ),
            "the `true` lemma must be reported inductive and propagated: {:?}",
            results[0]
        );
        assert!(
            matches!(
                results[1],
                WorkResult::NotInductive { lemma_id } if lemma_id == noninductive_id
            ),
            "the `x = 0` lemma must be reported NOT inductive, not \
             fabricated as propagated: {:?}",
            results[1]
        );
    }
}
