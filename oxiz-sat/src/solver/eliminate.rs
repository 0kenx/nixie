//! Inprocessing bounded variable elimination – a port of CaDiCaL `elim.cpp`
//! (with the backward-subsumption half of `backward.cpp`).
//!
//! This replaces the old one-shot `bve.rs` pass at the `enable_bve` call
//! sites.  Key properties (all faithful to cadical):
//!
//! * occurrence-list driven over *original* clauses, with per-literal
//!   occurrence counts maintained incrementally during the round;
//! * a work-list schedule ordered by elimination score; variables are
//!   *re-entered* whenever one of their clauses is removed or shrunk
//!   (on-the-fly self-subsumption, backward subsumption, eager unit
//!   propagation);
//! * the SatELite bound is `resolvents <= pos + neg + elimbound` with a
//!   per-resolvent size cap (`elimclslim` = 100) and an occurrence cap
//!   (`elimocclim` = 100);
//! * the elimination bound grows geometrically (0, 1, 2, 4, …, 16) whenever a
//!   phase completes without new candidates, re-arming every active variable
//!   (GlueMiniSat / COMinisatPS pioneering, cadical
//!   `increase_elimination_bound`);
//! * newly added resolvents run through *backward subsumption and
//!   strengthening* against the occurrence lists, so resolvents immediately
//!   shrink the database instead of growing it;
//! * re-armed from the search's conflict handler whenever new units were
//!   fixed or original clauses were removed/shrunk since the last phase
//!   (cadical `ineliminating`), not just once pre-search.
//!
//! Soundness gates (all checked in [`Solver::eliminate_phase`]):
//! decision level 0, base assertion scope, no real theory attached, no proof
//! logging (DRAT/LRAT), no assumptions in flight, not already UNSAT.
//! Model reconstruction reuses the well-tested `bve_def`/`bve_order`
//! extension machinery (see `save_model`): for every eliminated variable the
//! *positive* clauses are snapshotted with the pivot stripped at elimination
//! time, and both polarities' clauses are deleted, so the snapshot is
//! immutable for the rest of the solve.
//!
//! Watches and the binary implication graph are deliberately *not* touched
//! during a phase (occurrence lists are the only index); the phase ends by
//! rebuilding both from scratch whenever anything changed.

use super::*;
use crate::literal::LBool;

use std::collections::BinaryHeap;

pub(super) use super::equiv::SubstOutcome;

/// cadical `elimocclim`: skip a variable whose heavier-side occurrence list
/// is longer than this.
const ELIM_OCC_LIMIT: usize = 100;
/// cadical `elimclslim`: a resolvent longer than this aborts the variable.
const ELIM_CLS_LIMIT: usize = 100;
/// cadical `elimrounds`: rounds of eliminate ↔ subsume inside one phase.
const ELIM_ROUNDS: usize = 2;
/// cadical `elimboundmax`: the elimination bound growth ceiling.
const ELIM_BOUND_MAX: i64 = 16;
/// Cap on back-to-back pre-search elimination phases (see
/// [`Solver::eliminating_presearch`]).
const ELIM_PRESEARCH_PHASES: u64 = 4;
/// Resolution budget floor/ceiling per round (cadical `elimmineff` /
/// `elimmaxeff` with `elimeffort` = 1.0).
const ELIM_MIN_EFFORT: u64 = 10_000_000;
const ELIM_MAX_EFFORT: u64 = 2_000_000_000;

/// Reusable buffers for backward subsumption (see `Eliminator::bw_*`).
struct BwScratch {
    lits: Vec<Lit>,
    marked: Vec<Lit>,
    cands: Vec<ClauseId>,
    dlits: Vec<Lit>,
}

/// Outcome of resolving two clauses during elimination.
enum ElimResolve {
    /// Tautology, satisfied antecedent, or applied on the fly (shrink/unit).
    Skip,
    /// The resolvent is the unit literal (already applied by the caller when
    /// eager).
    Unit(Lit),
    /// A non-tautological resolvent with these literals.
    Resolvent(SmallVec<[Lit; 8]>),
}

/// Elimination score rank for the schedule heap: smaller = tried earlier.
/// Pure literals rank first (`0` bucket, most occurrences = smallest),
/// then ascending `pos*neg + pos + neg` (cadical `compute_elim_score`).
#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct ElimRank(u8, u64);

impl ElimRank {
    fn of(pos: u32, neg: u32) -> Self {
        if pos == 0 || neg == 0 {
            // More occurrences on the present side = more negative score in
            // cadical = popped earlier.
            ElimRank(0, (pos.max(neg) as u64) << 32)
        } else {
            let prod = u64::from(pos) * u64::from(neg);
            let sum = u64::from(pos + neg);
            ElimRank(1, prod + sum)
        }
    }
}

/// Per-phase scratch state for the eliminator. Only alive during an
/// elimination phase; `occs`/`noccs`/`val`/`mark` are indexed by literal code.
struct Eliminator {
    /// Occurrence lists over original clauses, connected on every literal
    /// (level-0-falsified entries included; the `val` checks filter them, as
    /// in cadical). Deletion is lazy – dead ids are skipped on access and
    /// compacted by [`Solver::elim_flush_sort_occs`].
    occs: Vec<Vec<ClauseId>>,
    /// Occurrence counts (cadical `noccs`) for unassigned literals.
    noccs: Vec<u32>,
    /// Literal values during the round: seeded from the level-0 trail and
    /// extended by units derived while eliminating (cadical keeps these on
    /// the trail and propagates eagerly through the occurrence lists).
    val: Vec<i8>,
    /// Signed marks over literal codes: +1 = literal marked, -1 = complement
    /// marked (same scheme as `subsume.rs`).
    mark: Vec<i8>,
    /// Elimination schedule (min-heap on `ElimRank`).
    schedule: BinaryHeap<std::cmp::Reverse<(ElimRank, u32)>>,
    /// Backward-subsumption work list of freshly added resolvents and
    /// shrunken clauses. Consumed FIFO through [`Self::bw_head`]: entries
    /// before the head are processed, the tail is pending.
    backward: Vec<ClauseId>,
    /// Read cursor into `backward` (persistent across
    /// [`Solver::elim_backward_clauses`] calls; see the drain note there).
    bw_head: usize,
    /// Units derived during the round, mirrored into `val` immediately and
    /// forced on the level-0 trail by the phase epilogue.
    units: SmallVec<[Lit; 32]>,
    /// Resolution steps consumed this round (cadical `stats.elimres`).
    resolutions: u64,
    /// Scratch buffers reused across backward-subsumption candidates (the
    /// per-candidate allocations dominated the phase cost: 67 % of profile
    /// time on `6s167-opt` was SmallVec collect/push inside
    /// `elim_backward_clause`).
    bw_lits: Vec<Lit>,
    bw_marked: Vec<Lit>,
    bw_dlits: Vec<Lit>,
    bw_cands: Vec<ClauseId>,
    /// Variables eliminated this round.
    eliminated: usize,
    /// Whether anything structurally changed (clause added/removed/shrunk),
    /// so the phase epilogue must rebuild watches.
    dirty: bool,
}

impl Eliminator {
    fn new(num_vars: usize, trail: &Trail) -> Self {
        let n = 2 * num_vars.max(1);
        let mut val = vec![0i8; n];
        // Seed from level-0 assignments (elimination only runs at level 0, so
        // the whole trail is unconditional).
        for &lit in trail.assignments() {
            val[lit.code() as usize] = 1;
            val[lit.negate().code() as usize] = -1;
        }
        Self {
            occs: vec![Vec::new(); n],
            noccs: vec![0; n],
            val,
            mark: vec![0; n],
            schedule: BinaryHeap::new(),
            backward: Vec::new(),
            bw_head: 0,
            units: SmallVec::new(),
            resolutions: 0,
            eliminated: 0,
            dirty: false,
            bw_lits: Vec::new(),
            bw_marked: Vec::new(),
            bw_dlits: Vec::new(),
            bw_cands: Vec::new(),
        }
    }

    #[inline]
    fn lit_val(&self, lit: Lit) -> i8 {
        self.val[lit.code() as usize]
    }
}

impl Solver {
    /// The `real_theory_attached` relaxation: destructive preprocessing is
    /// safe under a real theory **iff** the caller froze the theory-mapped
    /// variables first — the passes skip frozen variables, so they only
    /// transform Boolean-structure variables the theory never observes.
    pub(super) fn destructive_preprocessing_safe(&self) -> bool {
        !self.real_theory_attached || self.theory_vars_frozen
    }

    /// Whether destructive inprocessing (elimination) may run right now.
    fn elimination_allowed(&self) -> bool {
        self.trail.decision_level() == 0
            && self.assertion_levels.len() <= 1
            && self.destructive_preprocessing_safe()
            && self.proof.is_none()
            && !self.lrat
            && !self.trivially_unsat
            // Assumption solving routes through the limited restart handler
            // and never reaches the inprocessing schedule, but stay
            // defensive: an eliminated variable can no longer be assumed.
            && !self.assumptions_active
    }

    /// Pre-search fixpoint gate: unlike [`Self::eliminating`], the conflict
    /// limit is ignored (no conflicts have happened yet). A phase runs while
    /// the previous one was productive (`last_elim_eliminated > 0`), bounded
    /// by a small phase cap: later phases re-scan the whole database for a
    /// handful of variables each (measured on `6s167-opt`: phase 1 eliminates
    /// 3250 of 4640 variables; phases 2-8 average ~50), so an unbounded
    /// fixpoint burns seconds of occurrence-list work the mid-search schedule
    /// would otherwise amortize.
    pub(super) fn eliminating_presearch(&self) -> bool {
        // `elimination_allowed` must gate here too: `eliminate_phase` refuses
        // to run (LRAT/proof attached, real theory, incremental scope) without
        // advancing `elim_phases`, so an unguarded loop would spin forever.
        self.config.enable_bve
            && self.elimination_allowed()
            && !self.elim_finished
            && self.elim_phases < ELIM_PRESEARCH_PHASES
            && (self.elim_phases == 0 || self.last_elim_eliminated > 0)
    }

    /// cadical `ineliminating`: the elimination conflict limit has passed and
    /// there is something new to eliminate (units fixed at level 0 or
    /// original clauses removed/shrunk since the last phase).
    pub(super) fn eliminating(&self) -> bool {
        if !self.config.enable_bve || self.elim_finished {
            return false;
        }
        if self.stats.conflicts < self.lim_elim {
            return false;
        }
        // Conflict scheduling (cadical parity): the first phase fires
        // unconditionally once the conflict limit is crossed — the pre-search
        // fixpoint that normally arms it via mark-all is skipped unless
        // `presearch_collapse` is set.
        if self.elim_phases == 0 && !self.config.presearch_collapse {
            return true;
        }
        self.last_elim_fixed
            < self
                .trail
                .level_start(1)
                .min(self.trail.assignments().len())
            || self.elim_mark_count > 0
    }

    /// Scheduled elimination entry for the conflict handler: backtracks to
    /// the root and runs one phase. Returns `Unsat` if elimination derived
    /// the empty clause.
    pub(super) fn try_scheduled_elimination(&mut self) -> SubstOutcome {
        if !self.eliminating() || !self.elimination_allowed() {
            return SubstOutcome::Ok;
        }
        if self.trail.decision_level() > 0 {
            self.backtrack_with_phase_saving(0);
        }
        self.eliminate_phase()
    }

    /// Mark every active variable for elimination (cadical's wholesale
    /// re-arm; used after probe rounds fix units).
    pub(super) fn mark_elim_all(&mut self) {
        for idx in 0..self.num_vars {
            self.mark_elim_one(Var::new(idx as u32));
        }
    }

    /// Mark every variable of `lits` as an elimination candidate (cadical
    /// `mark_elim`). Called when an original clause is removed or shrunk.
    pub(super) fn mark_elim_vars(&mut self, lits: impl IntoIterator<Item = Lit>) {
        for lit in lits {
            let v = lit.var();
            self.mark_elim_one(v);
        }
    }

    fn mark_elim_one(&mut self, v: Var) {
        let i = v.index();
        if i >= self.elim_mark.len() || self.elim_mark[i] {
            return;
        }
        if self.trail.is_assigned(v) || self.var_eliminated(v) {
            return;
        }
        // Freeze set: theory-mapped variables are never eliminated (their
        // assignments surface to the theory, and the SMT layer's
        // term-to-var maps would dangle).
        if self.frozen_vars.contains(&v) {
            return;
        }
        self.elim_mark[i] = true;
        self.elim_mark_count += 1;
    }

    /// One elimination *phase* (cadical `elim`): alternate elimination rounds
    /// with subsumption rounds until nothing changes or the round limit is
    /// hit, then grow the elimination bound if the phase completed and
    /// reschedule every active variable.
    pub(super) fn eliminate_phase(&mut self) -> SubstOutcome {
        if !self.elimination_allowed() {
            return SubstOutcome::Ok;
        }
        self.elim_mark.resize(self.num_vars, false);
        self.elim_var_flag.resize(self.num_vars, false);
        self.bve_def.resize(self.num_vars, Vec::new());

        // The very first phase schedules every active variable (cadical's
        // fresh-variable flags start marked).
        if self.elim_phases == 0 {
            for idx in 0..self.num_vars {
                self.mark_elim_one(Var::new(idx as u32));
            }
        }

        // cadical backtracks and propagates first; we are already at level 0
        // and propagated (the schedule only runs post-conflict at the root or
        // pre-search), but re-propagating is cheap and rules out staleness.
        if self.propagate().is_some() {
            self.trivially_unsat = true;
            return SubstOutcome::Unsat;
        }

        self.elim_phases += 1;
        #[cfg(feature = "std")]
        if std::env::var("OXIZ_LOG_ELIM").is_ok() {
            eprintln!(
                "[elim] phase {} start: conflicts={} vars={} orig={}",
                self.elim_phases,
                self.stats.conflicts,
                self.num_vars,
                self.clauses.num_original()
            );
        }

        // Make sure a subsumption round ran since the last elimination phase
        // (cadical: `if (last.elim.subsumephases == stats.subsumephases)
        // subsume ()`).
        let (mut subsumed, mut strengthened) = self.subsume_round();
        #[cfg(feature = "std")]
        if std::env::var("OXIZ_LOG_ELIM").is_ok() {
            eprintln!(
                "[elim]   pre-phase subsume_round: subsumed={} strengthened={}",
                subsumed, strengthened
            );
        }
        if self.trivially_unsat {
            return SubstOutcome::Unsat;
        }

        let mut phase_complete = false;
        let mut round = 1usize;
        let mut eliminated_total = 0usize;
        let mut dirty = subsumed > 0 || strengthened > 0;

        loop {
            let (eliminated, complete, round_dirty, units) = self.elim_round();
            #[cfg(feature = "std")]
            if std::env::var("OXIZ_LOG_ELIM").is_ok() {
                eprintln!(
                    "[elim]   round {}: eliminated={} complete={} dirty={} units={} resolutions={}",
                    round,
                    eliminated,
                    complete,
                    round_dirty,
                    units.len(),
                    self.elim_resolutions_total
                );
            }
            eliminated_total += eliminated;
            dirty |= round_dirty;

            // Force the units derived during the round on the level-0 trail
            // and propagate (watches are still stale for clauses the round
            // rewrote, so rebuild first when anything changed).
            if dirty {
                self.rebuild_watches_and_binary_graph();
            }
            for &lit in &units {
                match self.trail.lit_value(lit) {
                    LBool::True => {}
                    LBool::False => {
                        self.trivially_unsat = true;
                        return SubstOutcome::Unsat;
                    }
                    LBool::Undef => self.trail.assign_decision(lit),
                }
            }
            let confl = self.propagate().is_some();
            if confl {
                self.trivially_unsat = true;
                return SubstOutcome::Unsat;
            }

            if !complete {
                break;
            }
            if round >= ELIM_ROUNDS {
                break;
            }
            round += 1;

            // Prioritize subsumption: if it removed or strengthened anything,
            // new elimination candidates exist, so run another round.
            let (s, st) = self.subsume_round();
            subsumed += s;
            strengthened += st;
            dirty |= s > 0 || st > 0;
            if self.trivially_unsat {
                return SubstOutcome::Unsat;
            }
            if s > 0 || st > 0 || self.elim_mark_count > 0 {
                continue;
            }
            phase_complete = true;
            break;
        }
        let _ = (subsumed, strengthened);

        if phase_complete {
            self.increase_elimination_bound();
        }

        self.last_elim_eliminated = eliminated_total as u64;
        self.stats.bve_eliminated += eliminated_total as u64;
        self.last_elim_fixed = self
            .trail
            .level_start(1)
            .min(self.trail.assignments().len());

        // cadical: `lim.elim = conflicts + elimint * (phases + 1)`.
        let interval = self.config.elim_interval * (self.elim_phases + 1);
        self.lim_elim = self.stats.conflicts.saturating_add(interval);

        if eliminated_total == 0 && phase_complete && self.elim_bound >= ELIM_BOUND_MAX {
            // Bound saturated and nothing left to try: stop scheduling.
            self.elim_finished = true;
        }

        if self.trivially_unsat {
            SubstOutcome::Unsat
        } else {
            SubstOutcome::Ok
        }
    }

    /// cadical `increase_elimination_bound`: 0 → 1 → 2 → 4 → … → 16, then
    /// reschedule every active uneliminated variable.
    fn increase_elimination_bound(&mut self) {
        if self.elim_bound >= ELIM_BOUND_MAX {
            return;
        }
        if self.elim_bound < 0 {
            self.elim_bound = 0;
        } else if self.elim_bound == 0 {
            self.elim_bound = 1;
        } else {
            self.elim_bound *= 2;
        }
        if self.elim_bound > ELIM_BOUND_MAX {
            self.elim_bound = ELIM_BOUND_MAX;
        }
        for idx in 0..self.num_vars {
            self.mark_elim_one(Var::new(idx as u32));
        }
    }

    /// Retire a clause for the eliminator, first re-pointing any live
    /// trail-reason reference to `Decision`. A retired clause can be the
    /// recorded propagation reason of an assigned literal (binary reasons
    /// escape the `lits[0]` invariant – the binary-graph path records
    /// either position; the satisfied-clause retirement hits this on
    /// level-0 facts). Level-0 facts never enter conflict analysis, so a
    /// Decision reason is semantically exact (cadical: `v.reason = level ?
    /// … : 0`), and the deleted-reason invariant stays intact.
    fn elim_retire(&mut self, cid: ClauseId) {
        self.retire_clause(cid);
    }

    /// One elimination round (cadical `elim_round`). Returns
    /// `(eliminated, completed, dirty, units)`; `completed` is true when the
    /// schedule was fully drained (the resolution budget was not hit).
    fn elim_round(&mut self) -> (usize, bool, bool, SmallVec<[Lit; 32]>) {
        // Budget (cadical `elimlimited`): delta = search ticks × 1.0 clamped
        // to [1e7, 2e9] resolutions. Generous: elimination that completes is
        // almost always a net win; the budget only guards the pathological
        // case of a huge unproductive schedule.
        let ticks = self.ticks_focused + self.ticks_stable;
        let delta = ticks.clamp(ELIM_MIN_EFFORT, ELIM_MAX_EFFORT);
        let resolution_limit = self.elim_resolutions_total.saturating_add(delta);

        let num_vars = self.num_vars;
        let mut ctx = Eliminator::new(num_vars, &self.trail);

        // Connect original clauses and count occurrences in ONE pass.
        // Satisfied clauses are retired immediately (before their literals
        // would be connected); clauses with falsified literals have their
        // remaining unassigned variables marked (simulating unit
        // propagation, cadical `elim.cpp` ~L820). The previous two-pass
        // shape (scan, then connect) walked the whole database twice per
        // round – the dominant cost of the pre-search fixpoint on large
        // formulas (measured 0.77 s vs cadical's ~0.03 s on 6s167) – for
        // no semantic difference: retiring and connecting happen on
        // disjoint clause sets within one iteration.
        let ids: Vec<ClauseId> = self.clauses.iter_ids().collect();
        for cid in ids {
            let lits: SmallVec<[Lit; 8]> = match self.clauses.get(cid) {
                Some(c) if !c.deleted && !c.learned && c.lits.len() >= 2 => {
                    c.lits.iter().copied().collect()
                }
                _ => continue,
            };
            let mut satisfied = false;
            let mut falsified = false;
            for &lit in &lits {
                match ctx.lit_val(lit) {
                    1 => satisfied = true,
                    -1 => falsified = true,
                    _ => {}
                }
            }
            if satisfied {
                self.elim_retire(cid);
                self.stats.deleted_clauses += 1;
                ctx.dirty = true;
                continue;
            }
            if falsified {
                for &lit in &lits {
                    if ctx.lit_val(lit) == 0 {
                        self.mark_elim_one(lit.var());
                    }
                }
            }
            for &lit in &lits {
                if ctx.lit_val(lit) == 0 {
                    let code = lit.code() as usize;
                    ctx.occs[code].push(cid);
                    ctx.noccs[code] += 1;
                }
            }
        }

        // Seed the schedule from the mark vector (cheapest first).
        for idx in 0..num_vars {
            if self.elim_mark[idx] {
                self.elim_mark[idx] = false;
                let rank = ElimRank::of(
                    ctx.noccs[Lit::pos(Var::new(idx as u32)).code() as usize],
                    ctx.noccs[Lit::neg(Var::new(idx as u32)).code() as usize],
                );
                ctx.schedule.push(std::cmp::Reverse((rank, idx as u32)));
            }
        }
        self.elim_mark_count = 0;

        while let Some(std::cmp::Reverse((_, v))) = ctx.schedule.pop() {
            if self.trivially_unsat || self.elim_resolutions_total >= resolution_limit {
                break;
            }
            self.elim_try_variable(&mut ctx, Var::new(v));
        }

        let completed = ctx.schedule.is_empty() && !self.trivially_unsat;
        let eliminated = ctx.eliminated;
        let dirty = ctx.dirty;
        let units = ctx.units;

        // cadical `mark_redundant_clauses_with_eliminated_variables_as_garbage`:
        // learned (redundant) clauses mentioning an eliminated variable are
        // optional consequences – retire them. This is a SOUNDNESS
        // requirement for model reconstruction, not hygiene: a live learned
        // clause over an eliminated variable is entailed by the original
        // formula, so any honest model must satisfy it, but `save_model`
        // reconstructs eliminated variables purely from the recorded
        // `bve_def` (which only covers original clauses) and can assign a
        // value that falsifies it – handing back a "model" that violates an
        // entailed clause and therefore an original clause (differential
        // fuzz + `crn_11_99_u`: learned binary (57∨1101) survived v57's
        // elimination and the reconstructed model falsified it). Learned
        // clauses never enter the occurrence lists, so elimination alone
        // never removes them.
        if eliminated > 0 {
            let doomed: Vec<ClauseId> = self
                .clauses
                .iter_ids()
                .filter(|&cid| {
                    self.clauses.get(cid).is_some_and(|c| {
                        !c.deleted
                            && c.learned
                            && c.lits.iter().any(|&l| self.var_eliminated(l.var()))
                    })
                })
                .collect();
            for cid in doomed {
                self.elim_retire(cid);
                self.stats.deleted_clauses += 1;
            }
            self.learned_clause_ids
                .retain(|&cid| self.clauses.get(cid).is_some_and(|c| !c.deleted));
        }

        self.elim_resolutions_total += ctx.resolutions;
        (eliminated, completed, dirty, units)
    }

    /// cadical `try_to_eliminate_variable`.
    fn elim_try_variable(&mut self, ctx: &mut Eliminator, v: Var) {
        if self.trail.is_assigned(v) || self.var_eliminated(v) {
            return;
        }
        let mut pivot = Lit::pos(v);
        self.elim_flush_sort_occs(ctx, pivot);
        self.elim_flush_sort_occs(ctx, pivot.negate());
        let mut pos = ctx.noccs[pivot.code() as usize] as usize;
        let mut neg = ctx.noccs[pivot.negate().code() as usize] as usize;
        if pos == 0 || neg == 0 {
            // Pure variable: leave it to the pure-literal pass (our model
            // reconstruction only covers resolution elimination).
            return;
        }
        if pos > neg {
            core::mem::swap(&mut pos, &mut neg);
            pivot = pivot.negate();
        }
        if neg > ELIM_OCC_LIMIT {
            return;
        }
        if ctx.lit_val(pivot) != 0 {
            return;
        }

        let mut collected: Vec<SmallVec<[Lit; 8]>> = Vec::new();
        if self.elim_resolvents_bounded(ctx, pivot, pos, neg, &mut collected) {
            self.elim_add_resolvents(ctx, &collected);
            self.elim_retire_pivot_clauses(ctx, pivot);
            self.elim_var_flag[v.index()] = true;
            ctx.eliminated += 1;
            ctx.dirty = true;
        }
        self.elim_backward_clauses(ctx);
    }

    /// Compact (drop deleted) and sort an occurrence list by clause size,
    /// ascending (cadical `clause_smaller_size`), and refresh the noccs count.
    ///
    /// Keys are **decorated**: clause sizes are read from the arena once per
    /// entry and the sort runs on the pre-extracted keys. Sorting with an
    /// arena-lookup key closure pays a dependent-load pointer chase per
    /// *comparison* (O(n log n) random arena accesses per list, twice per
    /// scheduled variable per round), which dominated elimination-heavy
    /// instances' profiles. Tie groups (equal size – and deleted clauses,
    /// both keyed `usize::MAX`) keep their occurrence-list order (stable
    /// sort); the previous `sort_unstable_by_key` left tie order to the
    /// sort algorithm's internals, so this changes which equal-size clause
    /// resolves first – an arbitrary-tie reordering, not a heuristic signal.
    fn elim_flush_sort_occs(&mut self, ctx: &mut Eliminator, lit: Lit) {
        let list = &mut ctx.occs[lit.code() as usize];
        if list.is_empty() {
            return;
        }
        let clauses = &self.clauses;
        let mut keyed: Vec<(usize, ClauseId)> = list
            .iter()
            .filter_map(|&cid| {
                if let Some(c) = clauses.get(cid)
                    && !c.deleted
                {
                    return Some((c.lits.len(), cid));
                }
                None
            })
            .collect();
        keyed.sort_by_key(|&(len, _)| len);
        list.clear();
        list.extend(keyed.into_iter().map(|(_, cid)| cid));
        ctx.noccs[lit.code() as usize] = list.len() as u32;
    }

    /// cadical `elim_resolvents_are_bounded`: try all resolutions between the
    /// pivot's clauses; abort as soon as a resolvent is too large or the
    /// non-tautological count exceeds `pos + neg + elimbound`. Units and
    /// self-subsumptions are applied eagerly while scanning.
    fn elim_resolvents_bounded(
        &mut self,
        ctx: &mut Eliminator,
        pivot: Lit,
        pos: usize,
        neg: usize,
        collected: &mut Vec<SmallVec<[Lit; 8]>>,
    ) -> bool {
        let bound = (pos + neg) as i64 + self.elim_bound;
        let ps: Vec<ClauseId> = ctx.occs[pivot.code() as usize].clone();
        let ns: Vec<ClauseId> = ctx.occs[pivot.negate().code() as usize].clone();
        let mut resolvents: i64 = 0;

        for &cid in &ps {
            if self.trivially_unsat {
                return false;
            }
            if self.clauses.get(cid).is_none_or(|c| c.deleted) {
                continue;
            }
            for &nid in &ns {
                if self.clauses.get(nid).is_none_or(|c| c.deleted) {
                    continue;
                }
                ctx.resolutions += 1;
                match self.elim_resolve_clauses(ctx, cid, pivot, nid) {
                    ElimResolve::Skip => {}
                    ElimResolve::Unit(u) => {
                        self.elim_assign_unit(ctx, u);
                        if self.trivially_unsat {
                            return false;
                        }
                    }
                    ElimResolve::Resolvent(r) => {
                        resolvents += 1;
                        if r.len() > ELIM_CLS_LIMIT || resolvents > bound {
                            return false;
                        }
                        collected.push(r);
                    }
                }
                if ctx.lit_val(pivot) != 0 {
                    return false;
                }
            }
        }
        true
    }

    /// Resolve clause `cid` (containing `pivot`) with clause `nid`
    /// (containing `¬pivot`) – cadical `resolve_clauses` with eager
    /// propagation. Satisfied antecedents are retired; self-subsumptions
    /// shrink the antecedent on the fly; units are reported to the caller.
    ///
    /// Structure: a **pure marking phase** that iterates both antecedents'
    /// literals directly in the arena (holding only `&self.clauses` – the
    /// previous shape copied each antecedent into a heap SmallVec per
    /// resolution, which dominated allocation profiles on elimination-heavy
    /// instances), followed by an **effect phase** that applies the deferred
    /// retire/shrink once the arena borrows have ended. Ordering is
    /// preserved: the eager form retired/shrank at exactly these return
    /// points, and nothing between the phases reads the affected state.
    fn elim_resolve_clauses(
        &mut self,
        ctx: &mut Eliminator,
        cid: ClauseId,
        pivot: Lit,
        nid: ClauseId,
    ) -> ElimResolve {
        // Deferred side effects from the marking phase.
        let mut retire: Option<ClauseId> = None;
        // A missing (already deleted) antecedent: Skip outright – the partial
        // resolvent built so far is NOT a resolution consequence and must
        // never reach the size checks below (an empty c-side would fabricate
        // `trivially_unsat`).
        let mut missing = false;
        // (clause, literal to drop) – the self-subsumption shrinks always
        // drop exactly one literal here (the pivot side).
        let mut shrink: Option<(ClauseId, Lit)> = None;

        // Marks: +1 on c's literals, -1 on their complements. The resolvent
        // accumulates c's unassigned non-pivot literals *and* d's unassigned
        // non-shared ones (cadical builds `clause` the same way – forgetting
        // the c side yields an over-strong clause and a false UNSAT).
        let mut s = 0usize;
        let mut marked: SmallVec<[Lit; 8]> = SmallVec::new();
        let mut resolvent: SmallVec<[Lit; 8]> = SmallVec::new();

        let mut t = 0usize;
        let mut tautological = false;

        // ---- pure marking phase (immutable arena borrows only) ----
        'phases: {
            let Some(c) = self.clauses.get(cid).filter(|c| !c.deleted) else {
                missing = true;
                break 'phases;
            };
            for &lit in c.lits.iter() {
                if lit == pivot {
                    s += 1;
                    continue;
                }
                match ctx.lit_val(lit) {
                    1 => {
                        // Antecedent satisfied: retire it.
                        retire = Some(cid);
                        break 'phases;
                    }
                    -1 => continue, // falsified: dropped from the resolvent
                    _ => {
                        ctx.mark[lit.code() as usize] = 1;
                        ctx.mark[lit.negate().code() as usize] = -1;
                        marked.push(lit);
                        resolvent.push(lit);
                        s += 1;
                    }
                }
            }

            let Some(d) = self.clauses.get(nid).filter(|c| !c.deleted) else {
                missing = true;
                break 'phases;
            };
            'd: for &lit in d.lits.iter() {
                if lit == pivot.negate() {
                    t += 1;
                    continue;
                }
                match ctx.lit_val(lit) {
                    1 => {
                        retire = Some(nid);
                        break 'phases;
                    }
                    -1 => continue,
                    _ => {
                        let m = ctx.mark[lit.code() as usize];
                        if m < 0 {
                            tautological = true;
                            break 'd;
                        }
                        if m == 0 {
                            resolvent.push(lit);
                        }
                        t += 1;
                    }
                }
            }
        }

        // ---- effect phase ----
        if missing {
            self.elim_unmark(ctx, &marked);
            return ElimResolve::Skip;
        }
        if let Some(r) = retire {
            self.elim_unmark(ctx, &marked);
            self.elim_retire_clause(ctx, r);
            return ElimResolve::Skip;
        }

        self.elim_unmark(ctx, &marked);

        if tautological {
            return ElimResolve::Skip;
        }

        let size = resolvent.len();
        if size == 0 {
            self.trivially_unsat = true;
            return ElimResolve::Skip;
        }
        if size == 1 {
            return ElimResolve::Unit(resolvent[0]);
        }

        // Double self-subsuming resolution: c and d are identical except for
        // the pivot; shrinking c (dropping the pivot) is equivalent to adding
        // the resolvent and deleting both clauses, and keeps the clause
        // instead of growing the database. (The double case `s > size &&
        // t > size` shrinks c, same as single-s-vs-c.)
        if s > size {
            shrink = Some((cid, pivot));
        }
        // Single self-subsuming resolution against d: drop ¬pivot from d.
        else if t > size {
            shrink = Some((nid, pivot.negate()));
        }
        if let Some((sid, drop_lit)) = shrink {
            self.elim_shrink_clause(ctx, sid, &[drop_lit]);
            return ElimResolve::Skip;
        }
        ElimResolve::Resolvent(resolvent)
    }

    /// Add the resolvents collected by [`Self::elim_resolvents_bounded`]
    /// (cadical `elim_add_resolvents`): each non-tautological resolvent
    /// (≥ 2 literals) becomes an original clause, connected into the
    /// occurrence lists and enqueued for backward subsumption.
    fn elim_add_resolvents(&mut self, ctx: &mut Eliminator, collected: &[SmallVec<[Lit; 8]>]) {
        for r in collected {
            if self.trivially_unsat {
                return;
            }
            // Satisfied resolvents are pointless (an antecedent was
            // satisfied during the scan and is being retired).
            if r.iter().any(|&l| ctx.lit_val(l) == 1) {
                continue;
            }
            let rid = self.clauses.add_original(r.iter().copied());
            for &lit in r {
                if ctx.lit_val(lit) == 0 {
                    let code = lit.code() as usize;
                    ctx.occs[code].push(rid);
                    ctx.noccs[code] += 1;
                }
            }
            ctx.backward.push(rid);
            ctx.dirty = true;
        }
    }

    /// Retire every original clause containing `±pivot`: snapshot the
    /// positive-polarity ones (pivot stripped) into `bve_def` for model
    /// reconstruction, mark all of them deleted, and reschedule the variables
    /// of their other literals.
    fn elim_retire_pivot_clauses(&mut self, ctx: &mut Eliminator, pivot: Lit) {
        // `pivot` may be the negated variable after the swap; `bve_def`
        // always records clauses that contained the *positive* variable
        // (the reconstruction in `save_model` is stated in those terms).
        let pos_lit = Lit::pos(pivot.var());
        for side in [pivot, pivot.negate()] {
            let ids: Vec<ClauseId> = ctx.occs[side.code() as usize].clone();
            for cid in ids {
                let lits: SmallVec<[Lit; 8]> = match self.clauses.get(cid) {
                    Some(c) if !c.deleted => c.lits.iter().copied().collect(),
                    _ => continue,
                };
                if !lits.contains(&side) {
                    continue;
                }
                if side == pos_lit {
                    let stripped: SmallVec<[Lit; 4]> =
                        lits.iter().copied().filter(|&l| l != side).collect();
                    self.bve_def[pivot.var().index()].push(stripped);
                }
                self.elim_retire_clause_lits(ctx, cid, &lits);
            }
            ctx.occs[side.code() as usize].clear();
            ctx.noccs[side.code() as usize] = 0;
        }
        self.bve_order.push(pivot.var());
    }

    /// Retire (mark deleted) one clause and reschedule the variables of all
    /// its literals (cadical `elim_update_removed_clause`).
    fn elim_retire_clause(&mut self, ctx: &mut Eliminator, cid: ClauseId) {
        let lits: SmallVec<[Lit; 8]> = match self.clauses.get(cid) {
            Some(c) if !c.deleted => c.lits.iter().copied().collect(),
            _ => return,
        };
        self.elim_retire_clause_lits(ctx, cid, &lits);
    }

    fn elim_retire_clause_lits(&mut self, ctx: &mut Eliminator, cid: ClauseId, lits: &[Lit]) {
        if self.clauses.get(cid).is_none_or(|c| c.deleted) {
            return;
        }
        self.clauses.mark_deleted_raw(cid);
        self.stats.deleted_clauses += 1;
        ctx.dirty = true;
        for &lit in lits {
            let code = lit.code() as usize;
            if ctx.noccs[code] > 0 {
                ctx.noccs[code] -= 1;
            }
            // Their occurrence counts just dropped: reschedule.
            self.mark_elim_one(lit.var());
        }
        // Physical removal from `occs` is lazy (filtered on access).
    }

    /// Drop `drop` from clause `cid` in place (cadical `strengthen_clause`
    /// during elimination), updating the occurrence counts of the removed
    /// literals and rescheduling the surviving clause's variables. A result
    /// of length 0/1 becomes UNSAT / an eagerly-applied unit.
    fn elim_shrink_clause(&mut self, ctx: &mut Eliminator, cid: ClauseId, drop: &[Lit]) {
        let lits: SmallVec<[Lit; 8]> = match self.clauses.get(cid) {
            Some(c) if !c.deleted => c.lits.iter().copied().collect(),
            _ => return,
        };
        // A clause that is currently the level-0 propagation reason of one of
        // its literals must not be rewritten in place: the reason pointer
        // would describe literals no longer in the clause. Level-0 reasons
        // are never read by conflict analysis (it only resolves on literals
        // above level 0), but keeping them intact costs nothing.
        for &lit in &lits {
            let var = lit.var();
            if self.trail.is_assigned(var)
                && matches!(self.trail.reason(var), Reason::Propagation(r) if r == cid)
            {
                return;
            }
        }
        let new_lits: SmallVec<[Lit; 8]> = lits
            .iter()
            .copied()
            .filter(|&l| !drop.contains(&l))
            .collect();
        match new_lits.len() {
            0 => {
                self.trivially_unsat = true;
                self.elim_retire_clause_lits(ctx, cid, &lits);
                return;
            }
            1 => {
                // Strengthened to a unit: apply it eagerly.
                let unit = new_lits[0];
                self.elim_retire_clause_lits(ctx, cid, &lits);
                self.elim_assign_unit(ctx, unit);
                return;
            }
            _ => {}
        }
        self.clauses.shrink(cid, &new_lits);
        // Recompute the stored LBD over the shrunken literal set (learned
        // clauses keep the `lbd <= len` invariant; originals have no LBD).
        if self.clauses.get(cid).is_some_and(|c| c.learned) {
            let lbd = self.compute_lbd(&new_lits);
            self.clauses.set_lbd(cid, lbd);
            self.clauses.assign_tier_from_lbd(cid);
        }
        ctx.dirty = true;
        for &lit in drop {
            let code = lit.code() as usize;
            // Physically remove the clause from the dropped literal's
            // occurrence list. A stale entry makes a later unit assignment
            // (`elim_assign_unit`) treat this clause as *satisfied* by a
            // literal it no longer contains and silently delete a live
            // constraint – a false SAT (caught by differential fuzz:
            // it143's model violated the entailed clause (9 ∨ ¬10) after
            // (9 ∨ ¬10 ∨ 5) shrank). Lazy deletion is only sound for
            // *retired* clauses, which the `!c.deleted` access filter
            // skips; a shrunken clause stays alive.
            if let Some(pos) = ctx.occs[code].iter().position(|&c| c == cid) {
                ctx.occs[code].swap_remove(pos);
            }
            if ctx.noccs[code] > 0 {
                ctx.noccs[code] -= 1;
            }
        }
        let mut vars: SmallVec<[Var; 8]> = SmallVec::new();
        if let Some(c) = self.clauses.get(cid) {
            for &lit in c.lits {
                vars.push(lit.var());
            }
        }
        for v in vars {
            self.mark_elim_one(v);
        }
        // The shrunken clause may now subsume others: queue it.
        ctx.backward.push(cid);
    }

    /// Assign a unit derived during elimination (cadical `assign_unit` +
    /// `elim_propagate`): update the scratch values, then eagerly simplify
    /// through the occurrence lists – clauses containing the literal are
    /// satisfied (retired), clauses containing its complement are shortened
    /// (which may produce further units).
    fn elim_assign_unit(&mut self, ctx: &mut Eliminator, lit: Lit) {
        match ctx.lit_val(lit) {
            1 => return,
            -1 => {
                self.trivially_unsat = true;
                return;
            }
            _ => {}
        }
        ctx.val[lit.code() as usize] = 1;
        ctx.val[lit.negate().code() as usize] = -1;
        ctx.units.push(lit);

        // Retire satisfied clauses.
        let ids: Vec<ClauseId> = ctx.occs[lit.code() as usize].clone();
        for cid in ids {
            self.elim_retire_clause(ctx, cid);
        }
        // Shorten clauses containing the complement.
        let neg = lit.negate();
        let ids: Vec<ClauseId> = ctx.occs[neg.code() as usize].clone();
        for cid in ids {
            let contains = self
                .clauses
                .get(cid)
                .is_some_and(|c| !c.deleted && c.lits.contains(&neg));
            if !contains {
                continue;
            }
            self.elim_shrink_clause(ctx, cid, &[neg]);
            if self.trivially_unsat {
                return;
            }
        }
    }

    /// cadical `elim_backward_clauses`: for every queued clause (fresh
    /// resolvents and shrunken clauses), look for connected clauses it
    /// subsumes or strengthens.
    ///
    /// The read cursor lives on the context (`bw_head`), not the call: the
    /// previous shape took the queue out with `mem::take`, processed it
    /// through a local index, and put the *whole* vector back – including
    /// the already-processed prefix – so every call re-processed the entire
    /// history (measured on `6s167-opt`: 12M processed entries for 12k
    /// enqueues, 99.9% of the first elimination phase's 630 ms).
    /// cadical's `Eliminator::dequeue` pops each entry, so each enqueue is
    /// processed exactly once; the persistent head + drain below give the
    /// same single-pass semantics while keeping pushes that arrive *during*
    /// processing (from `elim_shrink_clause` / unit cascades) in the same
    /// drain, exactly like cadical's single shared queue.
    fn elim_backward_clauses(&mut self, ctx: &mut Eliminator) {
        while ctx.bw_head < ctx.backward.len() && !self.trivially_unsat {
            let cid = ctx.backward[ctx.bw_head];
            ctx.bw_head += 1;
            self.elim_backward_clause(ctx, cid);
        }
        if ctx.bw_head == ctx.backward.len() {
            ctx.backward.clear();
            ctx.bw_head = 0;
        }
    }

    fn elim_backward_clause(&mut self, ctx: &mut Eliminator, cid: ClauseId) {
        let mut scratch = BwScratch {
            lits: core::mem::take(&mut ctx.bw_lits),
            marked: core::mem::take(&mut ctx.bw_marked),
            cands: core::mem::take(&mut ctx.bw_cands),
            dlits: core::mem::take(&mut ctx.bw_dlits),
        };
        self.elim_backward_clause_inner(ctx, cid, &mut scratch);
        ctx.bw_lits = scratch.lits;
        ctx.bw_marked = scratch.marked;
        ctx.bw_cands = scratch.cands;
        ctx.bw_dlits = scratch.dlits;
    }

    #[expect(clippy::too_many_lines)]
    fn elim_backward_clause_inner(
        &mut self,
        ctx: &mut Eliminator,
        cid: ClauseId,
        scratch: &mut BwScratch,
    ) {
        scratch.lits.clear();
        scratch.marked.clear();
        scratch.cands.clear();
        match self.clauses.get(cid) {
            Some(c) if !c.deleted && !c.learned => scratch.lits.extend(c.lits.iter().copied()),
            _ => return,
        }
        let lits: &[Lit] = &scratch.lits;
        // Mark the candidate's unassigned literals; find the rarest one.
        let mut best: Option<Lit> = None;
        let mut best_len = usize::MAX;
        let mut size = 0usize;
        for &lit in lits {
            match ctx.lit_val(lit) {
                1 => {
                    self.elim_unmark(ctx, &scratch.marked);
                    self.elim_retire_clause(ctx, cid);
                    return;
                }
                -1 => continue,
                _ => {
                    let len = ctx.occs[lit.code() as usize].len();
                    if len < best_len {
                        best_len = len;
                        best = Some(lit);
                    }
                    ctx.mark[lit.code() as usize] = 1;
                    ctx.mark[lit.negate().code() as usize] = -1;
                    scratch.marked.push(lit);
                    size += 1;
                }
            }
        }
        let Some(best) = best else {
            self.elim_unmark(ctx, &scratch.marked);
            return;
        };
        if best_len > ELIM_OCC_LIMIT {
            self.elim_unmark(ctx, &scratch.marked);
            return;
        }

        scratch
            .cands
            .extend(ctx.occs[best.code() as usize].iter().copied());
        let cand_count = scratch.cands.len();
        for di in 0..cand_count {
            let did = scratch.cands[di];
            if did == cid {
                continue;
            }
            scratch.dlits.clear();
            match self.clauses.get(did) {
                Some(c) if !c.deleted && !c.learned => scratch.dlits.extend(c.lits.iter().copied()),
                _ => continue,
            }
            if scratch.dlits.len() < size {
                continue;
            }
            let mut negated: Option<Lit> = None;
            let mut found = 0usize;
            let mut satisfied = false;
            'dl: for &lit in scratch.dlits.iter() {
                match ctx.lit_val(lit) {
                    1 => {
                        satisfied = true;
                        break 'dl;
                    }
                    -1 => continue,
                    _ => {}
                }
                let m = ctx.mark[lit.code() as usize];
                if m == 0 {
                    continue;
                }
                if m < 0 {
                    if negated.is_some() {
                        found = 0; // two complemented literals: no match
                        break 'dl;
                    }
                    negated = Some(lit);
                }
                found += 1;
                if found == size {
                    break 'dl;
                }
            }
            if satisfied {
                self.elim_retire_clause(ctx, did);
                continue;
            }
            if found < size {
                continue;
            }
            match negated {
                None => {
                    // d is subsumed by the candidate: retire d.
                    self.stats.subsumed_removed += 1;
                    self.elim_retire_clause(ctx, did);
                }
                Some(neg) => {
                    // Self-subsuming resolution: strengthen d by dropping
                    // `neg`, or derive a unit (cadical's hyper unary
                    // resolution analysis).
                    let mut unit: Option<Lit> = None;
                    let mut ambiguous = false;
                    let mut d_satisfied = false;
                    for &lit in scratch.dlits.iter() {
                        match ctx.lit_val(lit) {
                            -1 => continue,
                            1 => {
                                d_satisfied = true;
                                break;
                            }
                            _ => {}
                        }
                        if lit == neg {
                            continue;
                        }
                        if unit.is_some() {
                            ambiguous = true;
                        } else {
                            unit = Some(lit);
                        }
                    }
                    if d_satisfied {
                        self.elim_retire_clause(ctx, did);
                    } else if let Some(u) = unit.filter(|_| !ambiguous) {
                        self.elim_assign_unit(ctx, u);
                        if self.trivially_unsat {
                            break;
                        }
                    } else if ctx.occs[neg.code() as usize].len() <= ELIM_OCC_LIMIT {
                        // `elim_shrink_clause` enqueues the strengthened
                        // clause on the shared backward queue itself (single
                        // enqueue site, so a clause is never queued twice for
                        // one strengthening).
                        self.elim_shrink_clause(ctx, did, &[neg]);
                        self.stats.self_subsumed += 1;
                    }
                }
            }
        }
        self.elim_unmark(ctx, &scratch.marked);
    }

    fn elim_unmark(&mut self, ctx: &mut Eliminator, marked: &[Lit]) {
        for &lit in marked {
            ctx.mark[lit.code() as usize] = 0;
            ctx.mark[lit.negate().code() as usize] = 0;
        }
    }
}
