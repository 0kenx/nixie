//! Incremental-probe state management.
//!
//! These helpers let a caller that drives the solver *incrementally* – asserting
//! more clauses and calling [`Solver::solve`] repeatedly – roll the search state
//! back to the committed (asserted) prefix after each probe.  They exist for the
//! bit-vector theory's embedded solver (`BvSolver::check`), whose probe pattern
//! exposes two ways a probe's residue can otherwise stay behind and turn a
//! genuinely-satisfiable formula into a false `Unsat`: the satisfying model left
//! on the trail (see [`Solver::restore_to_trail_size`]) and clauses learned while
//! an unjustified level-0 unit constraint was on the trail (see
//! [`Solver::forget_learned_since`]).
//!
//! It also holds the clause retraction those rollbacks share
//! ([`Solver::retract_clauses`]: `pop`'s scope and `forget_learned_since`'s
//! probe tail).

use super::*;

/// An implication list holding at most this many live edges is cleared of the
/// batch's edges by the per-edge removal
/// ([`BinaryImplicationGraph::remove_clause_edges_short`]), however many of
/// the batch's clauses it holds: at most this many edges squared element
/// visits (64) per list, against the per-edge bookkeeping of the batched
/// pass (see [`Solver::retract_clauses`]).
const RETRACT_PER_EDGE_MAX_LEN: usize = 8;

/// Scratch of [`Solver::retract_clauses`] (see `Solver::retract_scratch`).
///
/// Kept across calls so a push / probe / pop loop does not re-allocate it:
/// the arrays are grown on demand and only the positions a batch touches
/// are written, so the memory beyond them stays untouched.
#[derive(Debug, Default)]
pub(crate) struct RetractScratch {
    /// Marked clause ids, by `ClauseId::index()` – the `dead` mark layout
    /// [`crate::solver::BinaryImplicationGraph::compact_dead`] reads.  Set
    /// for the ids a batch is retracting through the batched pass (and for
    /// every id of the batch when the learned-clause registry is filtered
    /// against it); all `false` between batches.
    pub(super) dead: Vec<bool>,
    /// Whether a trigger literal has an entry in `triggers` and that entry
    /// has not been handled yet (by `Lit::code()`).  All `false` between
    /// batches.
    pub(super) trigger_pending: Vec<bool>,
    /// One `(trigger literal, clause)` per edge of a batch binary clause on
    /// a LONG list ([`RETRACT_PER_EDGE_MAX_LEN`]), in clause order: a
    /// trigger's FIRST entry names its first batch clause, every later one
    /// records that the list holds several ([`ClauseId::NULL`]).
    pub(super) triggers: Vec<(Lit, ClauseId)>,
}

impl Solver {
    /// Number of learned clauses currently tracked.
    ///
    /// Paired with [`Self::forget_learned_since`] to let an incremental caller
    /// drop exactly the clauses a single [`Self::solve`] added.
    #[must_use]
    pub fn learned_clause_count(&self) -> usize {
        self.learned_clause_ids.len()
    }

    /// Forget every learned clause recorded after `checkpoint`
    /// (a value previously returned by [`Self::learned_clause_count`]).
    ///
    /// Clause learning in CDCL is normally a sound optimisation, but the
    /// bit-vector theory drives this SAT solver *incrementally* in a way that
    /// breaks that invariant: `assert_const` / `assert_eq` install their unit
    /// constraints as level-0 trail assignments with `reason = Decision` and
    /// **no backing clause**.  Conflict analysis treats such a level-0 literal
    /// as an unjustified decision, so a clause learned while it is on the trail
    /// silently depends on it; once [`Self::restore_to_trail_size`] rolls that
    /// assignment off the trail at the end of a probe, the retained learned
    /// clause is missing a hypothesis and can spuriously force `Unsat` on the
    /// next probe.  `BvSolver::check()` therefore discards each probe's learned
    /// clauses, keeping only the asserted (original) clauses as the sound,
    /// reusable core.
    pub fn forget_learned_since(&mut self, checkpoint: usize) {
        if checkpoint >= self.learned_clause_ids.len() {
            return;
        }
        let to_remove: Vec<ClauseId> = self.learned_clause_ids.split_off(checkpoint);
        // Purges each forgotten clause's binary-implication-graph edges
        // before removing it (the graph is a direct fast-path index that, at
        // its hot-loop call sites, trusts its edges; a stale edge for a
        // forgotten binary learned clause would keep implying/conflicting
        // after the clause is gone) and records each deletion in the DRAT
        // proof (no-op unless enabled) while the literals are live.  The
        // tail was split off the registry above, so there is nothing left
        // to filter.
        self.retract_clauses(&to_remove, false);
    }

    /// Retract a batch of clauses: for every binary clause in `ids`, its
    /// binary-implication-graph edges; then, for every clause in `ids` in
    /// order, its DRAT deletion record (while its literals are still
    /// readable) and its removal from the clause database.
    ///
    /// On the graph, a list holding two or more of the batch's edges is
    /// compacted once ([`BinaryImplicationGraph::remove_marked_edges`]):
    /// the per-clause removal rescans the list for each of them, which is
    /// quadratic while the batch's clauses share a trigger – 16,000 binary
    /// clauses under one trigger took 28 ms to pop against 0.2 ms when
    /// their triggers were disjoint, and a real scope (a search's learned
    /// clauses over an asserted formula of bit-blasted gates) is the
    /// shared-trigger shape.  Every other list keeps the per-edge removal,
    /// which is the cheaper constant there: the short ones
    /// ([`RETRACT_PER_EDGE_MAX_LEN`]) as they are met, a long one when its
    /// single batch edge is known to stand alone.  Either way the surviving
    /// edge sequence is the one the per-clause removals leave: both drop
    /// exactly this batch's edges and keep every other edge in place.
    ///
    /// With `filter_learned`, the learned-clause registry is filtered
    /// against the batch's marks once (`pop`), instead of once per
    /// retracted clause – the larger of the two quadratic terms: a scope of
    /// 80,000 clauses with 4,245 registered learned clauses compared 340
    /// million times, 86 ms per pop.
    ///
    /// A null or already-removed id is skipped by the parts that would read
    /// its clause, as the per-clause code did.
    pub(super) fn retract_clauses(&mut self, ids: &[ClauseId], filter_learned: bool) {
        let mut scratch = core::mem::take(&mut self.retract_scratch);
        let RetractScratch {
            dead,
            trigger_pending,
            triggers,
        } = &mut scratch;
        triggers.clear();
        let mut any_marked = false;
        let mark = |dead: &mut Vec<bool>, id: ClauseId, any_marked: &mut bool| {
            if id.index() >= dead.len() {
                dead.resize(id.index() + 1, false);
            }
            dead[id.index()] = true;
            *any_marked = true;
        };
        // A registry filter reads every id of the batch, so they all go
        // into the marks; otherwise only the ids sent through the batched
        // pass below are marked, as they are met.
        let mark_all = filter_learned && !self.learned_clause_ids.is_empty();
        // One pass, in the per-clause order: a binary clause's edges (read
        // while its literals still are), then its proof deletion and its
        // removal from the database.
        for &id in ids {
            if id.is_null() {
                continue;
            }
            if mark_all {
                mark(dead, id, &mut any_marked);
            }
            let binary = self
                .clauses
                .get(id)
                .filter(|c| c.lits.len() == 2 && !c.deleted)
                .map(|c| (c.lits[0], c.lits[1]));
            if let Some((a, b)) = binary {
                for trigger in [a.negate(), b.negate()] {
                    if self.binary_graph.remove_clause_edges_short(
                        trigger,
                        id,
                        RETRACT_PER_EDGE_MAX_LEN,
                    ) {
                        continue;
                    }
                    if !mark_all {
                        mark(dead, id, &mut any_marked);
                    }
                    if trigger_pending.len() < 2 * self.num_vars {
                        trigger_pending.resize(2 * self.num_vars, false);
                    }
                    let pending = &mut trigger_pending[trigger.code() as usize];
                    triggers.push((trigger, if *pending { ClauseId::NULL } else { id }));
                    *pending = true;
                }
            }
            self.drat_delete(id);
            self.clauses.remove(id);
        }
        // Walk the collected entries backwards.  A trigger's LAST entry is
        // then the first one reached, and it says which removal the list
        // takes; the flag clears there, so the trigger's earlier entries –
        // reached afterwards – find it clear and skip.  Every collected
        // trigger has an entry, so every flag is back to `false` at the
        // end.  (A long list is only shortened here, so no edge of it was
        // sent down the per-edge path above.)
        for &(trigger, sole) in triggers.iter().rev() {
            let pending = &mut trigger_pending[trigger.code() as usize];
            if !*pending {
                continue;
            }
            *pending = false;
            if sole.is_null() {
                self.binary_graph.remove_marked_edges(dead, trigger);
            } else {
                self.binary_graph.remove_clause_edges(trigger, sole);
            }
        }
        if mark_all {
            self.learned_clause_ids
                .retain(|&id| !dead.get(id.index()).copied().unwrap_or(false));
        }
        if any_marked {
            for &id in ids {
                if let Some(marked) = dead.get_mut(id.index()) {
                    *marked = false;
                }
            }
        }
        self.retract_scratch = scratch;
    }

    /// Current trail size (number of assigned literals across all levels).
    ///
    /// Combined with [`Self::restore_to_trail_size`] this lets an incremental
    /// caller (e.g. the bit-vector theory's embedded solver) snapshot the
    /// committed assignment prefix before a [`Self::solve`] call and roll the
    /// trail back to it afterwards, discarding every search-derived assignment
    /// the solve added (decisions, propagations, learned-unit assignments).
    #[must_use]
    pub fn trail_size(&self) -> usize {
        self.trail.size()
    }

    /// Roll the trail back to a previously captured [`Self::trail_size`].
    ///
    /// This unassigns every literal added after `trail_size` (re-inserting the
    /// freed variables into the decision heaps so a later solve can branch on
    /// them again) and resets the decision level to 0.  It does **not** touch
    /// the clause database, so all originally-asserted constraints – and any
    /// clauses learned so far – remain in force; only the working assignment is
    /// reset to the committed prefix.
    ///
    /// Crucially this is how `BvSolver::check()` avoids letting one
    /// satisfiability probe leave a *model-specific* (and therefore unsound for
    /// the next, augmented, probe) assignment pinned at decision level 0:
    /// `solve()` does not reset the persisted trail on entry, so without this
    /// rollback the model chosen for probe *k* (including its level-0 decisions)
    /// would survive into probe *k+1* and could spuriously contradict a freshly
    /// asserted constraint, yielding a false `Unsat`.
    pub fn restore_to_trail_size(&mut self, trail_size: usize) {
        let current_size = self.trail.size();
        if current_size <= trail_size {
            // Nothing search-derived to discard; just make sure we are at the
            // root decision level so the next solve starts cleanly.
            self.backtrack_with_phase_saving(0);

            // Re-arm propagation over the retained prefix, exactly as the
            // size-based rollback below does.
            //
            // It is tempting to skip the rewind here on the grounds that
            // `backtrack_with_phase_saving` already clamps the head to the
            // rollback boundary – but that clamp is a *no-op when the search is
            // already at level 0*, which is precisely the state this branch
            // sees. A probe whose `solve()` ended in a level-0 conflict returns
            // without growing the trail (so `current_size == trail_size`) and
            // without backtracking, leaving the head parked past a literal whose
            // watch list was abandoned mid-scan. Rewinding guarantees the next
            // `solve()` re-derives the whole prefix's consequences whatever the
            // previous probe did.
            self.trail.reset_propagation_head();
            self.replay_root_units();
            return;
        }

        // Collect the variables that will be unassigned so they can be put back
        // into the decision heaps (mirrors the bookkeeping in `pop`).
        let mut unassigned_vars: Vec<Var> = Vec::with_capacity(current_size - trail_size);
        let assignments = self.trail.assignments();
        for &lit in &assignments[trail_size..current_size] {
            unassigned_vars.push(lit.var());
        }

        // `backtrack_to_size` clears the values and resets the level to 0 but
        // does not re-insert the freed variables into the decision heaps.
        self.trail.backtrack_to_size(trail_size);
        // The conflict-free prefix cannot reach past the surviving trail
        // (same clamp every solver backtrack applies).
        self.no_conflict_until = self.no_conflict_until.min(trail_size);

        // `backtrack_to_size` parks the propagation head at the end of the
        // surviving trail – correct for ordinary CDCL backtracking, where every
        // surviving literal has already been propagated *and its consequences
        // are still on the trail*.  That does not hold here: the discarded
        // suffix includes level-0 consequences of the retained prefix (e.g. the
        // bits a bit-blasted comparator derived from a pinned `assert_const`
        // operand), so leaving the head at the end tells the next `solve()`
        // that a prefix whose implications have just been erased is fully
        // propagated.  The solve then starts with no unit information at all and
        // has to rediscover it by search – turning a propagation-only refutation
        // into an exponential one (observed as multi-second `unsat` answers for
        // 24-bit bit-vector comparisons, and timeouts at 32 bits).  Rewinding
        // the head re-derives the prefix's consequences on the next propagate;
        // re-propagating an already-assigned literal is a no-op, so this is free
        // of semantic effect.
        self.trail.reset_propagation_head();

        for var in unassigned_vars {
            self.proof_set_unit_id(Lit::pos(var).to_dimacs(), 0);
            self.proof_set_unit_id(Lit::neg(var).to_dimacs(), 0);
            if !self.vsids.contains(var) {
                self.vsids.insert(var);
            }
            if !self.chb.contains(var) {
                self.chb.insert(var);
            }
            self.lrb.unassign(var);
        }
        self.replay_root_units();
    }

    /// Assign `lits` at decision level 0 and propagate to a fixpoint,
    /// without running a search.
    ///
    /// This is the external bit-blaster's evaluation primitive: it derives
    /// everything the current clause database entails about the assignment
    /// (every gate variable of a bit-blasted circuit settles), which the
    /// caller can read through [`Self::trail`] before rewinding with
    /// [`Self::restore_to_trail_size`] to the size captured before the
    /// call.  Returns `false` when propagation hits a conflict – the trail
    /// is then left at the conflict point, and the same rewind restores a
    /// clean state (the caller normally treats a conflict here as "the
    /// proposed guiding assignment is not a model; skip the guidance").
    ///
    /// Literals already assigned on the trail are skipped when they agree
    /// with the request; a disagreeing already-assigned literal returns
    /// `false` without assigning anything.
    pub fn assign_and_propagate_level0(&mut self, lits: &[Lit]) -> bool {
        for &lit in lits {
            match self.trail.lit_value(lit) {
                LBool::True => {}
                LBool::False => return false,
                LBool::Undef => self.trail.assign_decision(lit),
            }
        }
        self.propagate().is_none()
    }
}
