//! Opt-in "decide these first" hint for the embedded SAT engine, built on
//! `oxiz-sat`'s pre-existing [`oxiz_sat::BranchingHeuristic`] extension
//! point (added for `oxiz-ml`; nothing here required touching `oxiz-sat`).
//!
//! # Why this is a config knob, not a default
//!
//! `oxiz-sat`'s `pick_branch_var` builds its candidate list – every
//! unassigned variable, scanned in full – before it ever calls the
//! heuristic's `select`, whenever *any* external heuristic is installed at
//! all (see `oxiz-sat/src/solver/decide.rs`). That scan happens on every
//! single decision, for every solve this `Solver` instance ever runs, once
//! it is wired in – the SAT engine has no cheaper "is there actually a
//! pending hint right now" fast path to skip it with, and `SolverConfig`'s
//! `external_branching` slot can only be set once, at construction (the
//! field is `pub(super)` inside `oxiz-sat`, so a later `set_config` call on
//! this crate's own `Solver` cannot retarget it either – matching the
//! pre-existing behaviour of `restart_strategy` and friends, which also only
//! take effect through `with_config`).
//!
//! A lookup-table-heavy formula's index domains are typically tiny, so this
//! trade is a clear win *for that shape*; an unrelated large formula that
//! never enables it pays nothing, and one that enables it anyway pays the
//! per-decision candidate scan whether or not a table ever shows up. That
//! asymmetry is why `Solver::flatten_lookup_spines` populates the priority
//! list but `enable_domain_first_branching` defaults to `false` – see
//! `SolverConfig`'s doc comment.
use std::sync::{Arc, Mutex};

use oxiz_sat::{BoxedBranchingHeuristic, BranchingHeuristic, Var};
use rustc_hash::FxHashSet;

use super::Solver;

/// The shared "decide these first" queue. `Solver` keeps a handle to the
/// same `Arc` the installed [`BranchingHeuristic`] reads, so
/// `flatten_lookup_spines` can push into it as tables are discovered without
/// touching `oxiz-sat` at all.
pub(super) type PriorityQueue = Arc<Mutex<Vec<Var>>>;

/// The [`BranchingHeuristic`] wrapping a [`PriorityQueue`]: picks the first
/// still-*candidate* variable in priority order, or defers to the built-in
/// VSIDS/LRB/CHB strategy (`None`) once every priority variable is either
/// assigned or not part of this decision's candidate set.
struct PriorityHeuristic {
    queue: PriorityQueue,
}

impl BranchingHeuristic for PriorityHeuristic {
    fn select(&mut self, candidates: &[Var], _scores: &[f64]) -> Option<Var> {
        let queue = self.queue.lock().ok()?;
        if queue.is_empty() {
            return None;
        }
        let candidate_set: FxHashSet<Var> = candidates.iter().copied().collect();
        queue.iter().copied().find(|v| candidate_set.contains(v))
    }
}

/// Build a fresh, empty priority queue and the boxed heuristic that reads
/// it, ready to hand the queue half to `Solver` and the heuristic half to
/// `oxiz_sat::SolverConfig::external_branching`.
pub(super) fn new_priority_branching() -> (PriorityQueue, BoxedBranchingHeuristic) {
    let queue: PriorityQueue = Arc::new(Mutex::new(Vec::new()));
    let heuristic: BoxedBranchingHeuristic = Arc::new(Mutex::new(PriorityHeuristic {
        queue: Arc::clone(&queue),
    }));
    (queue, heuristic)
}

impl Solver {
    /// Append variables to the branch-priority queue, in order,
    /// skipping any already present. No-op (cheap: one lock, no allocation
    /// beyond what is pushed) when [`super::types::SolverConfig::enable_domain_first_branching`]
    /// was never turned on, since then the queue was never wired into the
    /// SAT engine at all and nothing ever reads it.
    pub(super) fn push_branch_priority(&self, vars: &[Var]) {
        let Ok(mut queue) = self.branch_priority.lock() else {
            return;
        };
        for &var in vars {
            if !queue.contains(&var) {
                queue.push(var);
            }
        }
    }
}
