//! The line between a *search* and the *goal* it searches, for
//! [`MBQIIntegration`].
//!
//! One `Solver::check` is one MBQI search.  Everything that search derives –
//! the ground terms it harvested from its own instantiations, the dedup filter
//! that stops a round re-deriving an earlier round's work, the one-shot
//! blind-instantiation guard, the round counter and its budget – belongs to
//! *that* search and must not be visible to the next one.  Everything the
//! caller put there – the registered quantifiers, the candidates from
//! `declare-const`, the configured limits, the cumulative statistics – belongs
//! to the goal and must survive.
//!
//! Getting that line wrong is task #28's third mechanism, and it goes wrong in
//! both directions at once: search residue left behind makes the next check on
//! an unchanged goal reach *further* (new terms, new SAT variables, new
//! original clauses, appearing several `check-sat` calls in), while the
//! accumulated round counter eventually crosses `max_rounds` and makes it reach
//! *nothing at all*.
//!
//! This module is that line, written down once:
//! [`MBQIIntegration::search_checkpoint`] takes the restore point and
//! [`MBQIIntegration::restore_search_state`] applies it.

use crate::prelude::*;
use nixie_core::sort::SortId;

use super::MBQIIntegration;
use crate::mbqi::conflict_driven::ConflictScores;
use crate::mbqi::heuristics::MBQIBudget;

/// A restore point for [`MBQIIntegration`]'s per-search state.
///
/// Produced by [`MBQIIntegration::search_checkpoint`] and consumed by
/// [`MBQIIntegration::restore_search_state`], which documents exactly what is
/// and is not restored.
#[derive(Debug, Clone, Default)]
pub struct MbqiSearchCheckpoint {
    /// Size of each per-sort extra-candidate pool before the search ran.
    candidate_pool_sizes: Vec<(SortId, usize)>,
}

impl MBQIIntegration {
    /// Total number of ground terms registered as instantiation candidates,
    /// across all sorts.
    ///
    /// Part of `Solver`'s goal fingerprint: `declare-const` registers a
    /// candidate without touching the assertion stack, so this is the counter
    /// that notices it.
    #[must_use]
    pub fn num_candidates(&self) -> usize {
        self.extra_candidates.values().map(Vec::len).sum()
    }

    /// Snapshot the state that belongs to *one* search, so it can be handed
    /// back after that search finishes.
    ///
    /// See [`Self::restore_search_state`] for what "belongs to one search"
    /// means and why the distinction matters.
    #[must_use]
    pub fn search_checkpoint(&self) -> MbqiSearchCheckpoint {
        MbqiSearchCheckpoint {
            candidate_pool_sizes: self
                .extra_candidates
                .iter()
                .map(|(&sort, terms)| (sort, terms.len()))
                .collect(),
        }
    }

    /// Return every field that describes the *progress of a search* to the
    /// state it had at `checkpoint`, keeping every field that describes the
    /// *goal*.
    ///
    /// # Which fields are which
    ///
    /// Goal state – untouched here: `quantifiers` (registered by `assert`, and
    /// retracted by `Solver::pop` through [`Self::truncate_quantifiers`]), the
    /// candidates registered outside a search (recorded in `checkpoint`), the
    /// configured limits, and `stats` (cumulative by contract).
    ///
    /// Search state – restored here:
    ///
    /// * `extra_candidates` beyond `checkpoint` – ground sub-terms harvested
    ///   from *this* search's own instantiation results so that a later round
    ///   of the same search can use them.
    /// * `generated_instantiations` – the dedup filter that stops a round from
    ///   re-deriving what an earlier round of the same search already derived.
    /// * `blind_attempted` – the one-shot guard for the blind-instantiation
    ///   fallback, which is meant to fire at most once *per search*.
    /// * `current_round` / `budget` / `conflict_scores` – the round counter that
    ///   `max_rounds` bounds, and the per-round budget it carves up.  [`Self::run`]
    ///   documents these as accumulating "for a single `solve()` invocation".
    /// * the instantiation engine's and lazy instantiator's caches.
    ///
    /// # Why it must be restored rather than left to accumulate
    ///
    /// Leaving it behind makes a repeated search on an *unchanged* goal do
    /// something different from the first one, in both directions.  Too much,
    /// at first: the dedup filter still holds the previous search's
    /// instantiations, so the next search skips them and reaches deeper,
    /// genuinely new terms – new SAT variables and new clauses appearing
    /// several `check-sat` calls into an unchanged session, which is the
    /// unexplained late-onset growth of task #28.  Then too little: once the
    /// accumulated `current_round` reaches `max_rounds`, every later search
    /// gives up before its first round and the goal silently stops being
    /// instantiated at all.
    ///
    /// Restoring costs no completeness: what is dropped is exactly what the
    /// finished search derived, so the next search on the same goal explores
    /// the same bounded space that this one did, and a search on a *changed*
    /// goal starts from the widened goal state that the change left behind.
    pub fn restore_search_state(&mut self, checkpoint: &MbqiSearchCheckpoint) {
        let mut pool_sizes: FxHashMap<SortId, usize> = FxHashMap::default();
        pool_sizes.extend(checkpoint.candidate_pool_sizes.iter().copied());
        self.extra_candidates.retain(|sort, terms| {
            match pool_sizes.get(sort) {
                Some(&len) => {
                    // The pools only ever grow by pushing, so truncating to the
                    // recorded length restores the pool exactly.
                    terms.truncate(len);
                    true
                }
                // Pool created during the search: it did not exist before it.
                None => false,
            }
        });

        self.generated_instantiations.clear();
        self.blind_attempted = false;
        self.current_round = 0;
        self.budget = MBQIBudget::new(self.budget.global_budget);
        self.conflict_scores = ConflictScores::new(self.conflict_scores.decay_factor);
        #[cfg(feature = "std")]
        {
            self.start_time = None;
        }
        self.instantiation_engine.clear_caches();
        self.lazy_instantiator.clear();
    }

    /// Test-only view of the fields [`Self::restore_search_state`] resets.
    ///
    /// Returned as a tuple of `(candidates, deduped_instantiations, round,
    /// blind_attempted)` so a regression pin can compare the state *after* a
    /// `check` against the state before it directly, rather than inferring it
    /// from clause counts.  See
    /// `crate::solver::scope_rebase_tests::a_check_leaves_the_mbqi_search_state_where_it_found_it`.
    #[cfg(test)]
    pub(crate) fn search_state_summary(&self) -> (usize, usize, usize, bool) {
        (
            self.num_candidates(),
            self.generated_instantiations.len(),
            self.current_round,
            self.blind_attempted,
        )
    }
}
