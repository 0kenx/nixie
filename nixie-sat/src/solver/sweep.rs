//! SAT sweeping with an embedded sub-solver (faithful port of kissat
//! `sweep.c`, kitten-based), plus its application through the existing
//! substitution path.
//!
//! # What the pass does
//!
//! For each candidate variable, a bounded **environment** — the original
//! clauses of its depth-≤2 cone, capped — is copied into a fresh kitten
//! (embedded CDCL, `crate::kitten`) formula. One kitten SAT solve over
//! the environment yields a witness; the witness's true literals seed
//! **backbone candidates** (literals true in this model that might be
//! true in *every* model) and an equivalence-candidate **partition**.
//! Each candidate is then *proved or refuted* with assumption solves:
//!
//! * backbone `l`: assume `¬l`; UNSAT ⇒ the formula entails `l` (a
//!   level-0 unit — extracted from the kitten clausal core and assigned).
//! * equivalence `a ≡ b`: two implication tests, assume `¬a, b` (b → a)
//!   and assume `a, ¬b` (a → b); both UNSAT ⇒ `a ≡ b`, proved by the
//!   kitten core of each test.
//!
//! SAT witnesses refine the candidate lists instead (a literal that can
//! be false is not a backbone; a class whose members took different
//! values splits), and in-model **flips** (`kitten_flip_literal`) shrink
//! the lists before any solve is spent.
//!
//! Proved equivalences are added to the main solver as the two entailed
//! binary clauses `(a ∨ ¬b)` and `(¬a ∨ b)`; the actual folding of
//! representatives through the clause database rides the existing
//! soundness-hardened substitution round
//! ([`Solver::substitute_equivalent_literals_round`], `solver/equiv.rs`)
//! — this port deliberately does **not** reimplement application.
//!
//! # Soundness
//!
//! * Environment copies drop literals that are false on the level-0
//!   trail and skip satisfied clauses, so every kitten clause is entailed
//!   by (original clause ∧ level-0 facts) — any kitten UNSAT result is a
//!   genuine consequence of the main formula.
//! * Only **original** (irredundant) clauses enter the environment
//!   (kissat sweeps in dense mode over irredundant clauses only).
//! * The pass runs at decision level 0, base assertion scope, with no
//!   proof tracer attached, no active assumptions, and only when
//!   destructive preprocessing is safe (no unfrozen real theory); see
//!   [`Solver::sweep_allowed`]. Every derived unit is assigned through
//!   the normal level-0 assign+propagate path — a conflict there is a
//!   genuine UNSAT over live clauses.
//! * Larger core lemmas are **not** added to the main database in this
//!   port: kissat adds them to checker/proof only
//!   (`add_core`'s `CHECK_AND_ADD_LITS`); with proofs gated off there is
//!   nothing to justify, so they are dropped (counted in stats).
//! * Work is bounded by **kitten ticks** (deterministic), never wall
//!   clock; the round budget is a per-mille slice of the effort-schedule
//!   window, mirroring kissat `sweepeffort` over `SET_EFFORT_LIMIT`.
//!
//! # Knobs (A/B infrastructure, default off)
//!
//! * `NIXIE_SWEEP=1` — enable the sweep (pre-search + each inprocessing
//!   round). Unset: every code path is inert (one cached `bool` load per
//!   round; trajectory-identical to base).
//! * `NIXIE_SWEEP_NULL=1` — matched null: identical machinery, budgets
//!   and candidate *set*, but the candidate *ranking* is scrambled by a
//!   deterministic hash of the variable index. The semantic content
//!   under test is candidate selection + proved equivalences; the null
//!   keeps the cost. (Verify the null actually fires: compare
//!   `kitten_solved` between arms before trusting any ratio.)
//! * `NIXIE_SWEEP_EFFORT=<permille>` — round tick budget override
//!   (default kissat `sweepeffort` = 100‰).
//! * `NIXIE_SWEEP_TRACE=1` — one telemetry line per round.
//!
//! # Port deviations from kissat (recorded)
//!
//! * Application of proved equivalences is deferred to the end of the
//!   round through the existing substitution round instead of kissat's
//!   per-equivalence `substitute_connected_clauses`; sound (the added
//!   binaries make the classes visible to the SCC) and it reuses the
//!   hardened rewrite, at the cost of possibly larger intermediate
//!   environments.
//! * kissat's `BUMP_DELAY(sweep)` schedule knob is not ported; the
//!   inprocessing round interval governs cadence.
//! * The occurrence-ranking key counts live original clauses over the
//!   BIG + watch lists (kissat counts one dense watch list; ours is
//!   BIG-authoritative), filtered the same way the environment build
//!   filters.

use super::*;
use crate::kitten::{INVALID, Kitten, KittenResult};
use crate::literal::LBool;
use smallvec::SmallVec;

/// kissat option defaults (`options.h`).
const SWEEP_VARS: u64 = 256;
const SWEEP_MAX_VARS: u64 = 8192;
const SWEEP_CLAUSES: u64 = 1024;
const SWEEP_MAX_CLAUSES: u64 = 32768;
const SWEEP_DEPTH: u64 = 2;
const SWEEP_MAX_DEPTH: u64 = 3;
const SWEEP_FLIP_ROUNDS: u32 = 1;
/// kissat `mineffort` floor for the effort reference (ticks).
const SWEEP_MIN_EFFORT: u64 = 1_000_000;

/// Outcome of a sweep round.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum SweepOutcome {
    /// Round completed (possibly budget-limited); formula alive.
    Ok,
    /// The round derived the empty clause (or a level-0 conflict).
    Unsat,
}

/// Per-round sweeper state (kissat `struct sweeper`). The kitten is
/// per-round: its tick counter *is* the round budget currency.
struct Sweeper {
    /// `depths[var]` = 1 + cone depth when the var is in the current
    /// environment (0 = not in it).
    depths: Vec<u32>,
    /// `reprs[lit_code]` = representative literal code of the equivalence
    /// class proved so far this round (identity when none).
    reprs: Vec<u32>,
    /// Intrusive scheduling ring over variables (`INVALID` = not
    /// scheduled).
    next: Vec<u32>,
    prev: Vec<u32>,
    first: u32,
    last: u32,
    /// Environment frontier variables (BFS order).
    vars: Vec<u32>,
    /// Large clauses copied into the current environment (ledger for the
    /// swept dedup, which the clear pass walks).
    refs: Vec<ClauseId>,
    /// Dedup set for `refs` (kissat's per-clause `swept` flag).
    swept: rustc_hash::FxHashSet<ClauseId>,
    /// Scratch clause under construction (literal codes).
    clause: Vec<u32>,
    /// Backbone candidates (literal codes).
    backbone: Vec<u32>,
    /// Equivalence-candidate partition, `INVALID`-separated classes.
    partition: Vec<u32>,
    /// Extracted core clause buffers, `INVALID`-separated.
    core: [Vec<u32>; 2],
    /// Which core buffer `save_core_clause` appends to.
    save: usize,
    /// Clauses encoded into kitten for the current environment.
    encoded: u32,
    kitten: Kitten,
    limit: SweepLimits,
}

struct SweepLimits {
    /// Round tick budget (kitten-internal ticks).
    ticks: u64,
    clauses: u64,
    depth: u64,
    vars: u64,
}

impl Solver {
    /// Whether the sweep may run right now (shared soundness gates).
    pub(super) fn sweep_allowed(&self) -> bool {
        self.trail.decision_level() == 0
            && self.assertion_levels.len() <= 1
            && self.proof.is_none()
            && !self.lrat
            && !self.trivially_unsat
            && !self.assumptions_active
            && self.destructive_preprocessing_safe()
    }

    /// Whether `var` is sweepable: in range, unassigned at level 0, not
    /// folded away by ELS/BVE/elimination (kissat `ACTIVE`).
    fn sweep_active(&self, var: u32) -> bool {
        let v = Var::new(var);
        (var as usize) < self.num_vars && !self.trail.is_assigned(v) && !self.var_eliminated(v)
    }

    /// Current value of a literal code as `i8` (`1/0/-1`).
    #[inline]
    fn sweep_value(&self, lit: u32) -> i8 {
        self.trail.lit_val(Lit::from_code(lit))
    }

    /// One full sweep round (`kissat_sweep`): schedule candidates, sweep
    /// each until the tick budget dies, apply the proved equivalences
    /// through the substitution round. `window` is the effort-schedule
    /// reference (search propagation since the last round; the pre-search
    /// call passes 0, floored at [`SWEEP_MIN_EFFORT`]).
    pub(super) fn sweep_round(&mut self, window: u64) -> SweepOutcome {
        if !crate::kitten_sweep_enabled() || !self.sweep_allowed() {
            return SweepOutcome::Ok;
        }
        let equivalences0 = self.stats.sweep_equivalences;
        let units0 = self.stats.sweep_units;

        let mut sweeper = Sweeper::new(self, window);
        let scheduled = sweeper.schedule_sweeping(self);
        let mut swept: u64 = 0;
        loop {
            if self.trivially_unsat {
                break;
            }
            if sweeper.kitten.stats.ticks >= sweeper.limit.ticks {
                break;
            }
            let Some(idx) = sweeper.next_scheduled() else {
                break;
            };
            if (idx as usize) < self.sweep_incomplete_flags.len() {
                self.sweep_incomplete_flags[idx as usize] = false;
            }
            self.sweep_one_variable(&mut sweeper, idx);
            swept += 1;
        }
        sweeper.unschedule_sweeping(self, swept, scheduled);
        // Trace values read before `release` consumes the sweeper.
        let trace_ticks = sweeper.kitten.stats.ticks;
        let trace_budget = sweeper.limit.ticks;
        let trace_solved = sweeper.kitten.stats.solved;
        let merged = sweeper.release(self);

        // Sum the sub-solver counters into the solver statistics
        // (kissat keeps `kitten_ticks`/`kitten_solved` solver-side).
        self.stats.kitten_ticks = self.stats.kitten_ticks.saturating_add(trace_ticks);
        self.stats.kitten_solved = self.stats.kitten_solved.saturating_add(trace_solved);
        self.stats.sweep_swept = self.stats.sweep_swept.saturating_add(swept);
        self.stats.sweep_rounds += 1;

        let equivalences = self.stats.sweep_equivalences - equivalences0;
        let units = self.stats.sweep_units - units0;

        if crate::kitten_sweep_trace_enabled() {
            #[cfg(feature = "std")]
            eprintln!(
                "c [sweep] vars={} scheduled={scheduled} swept={swept} equivalences={equivalences} \
                 units={units} merged={merged} kitten_ticks={} budget={} env_vars={} \
                 env_clauses={} solved={}",
                self.num_vars,
                trace_ticks,
                trace_budget,
                self.stats.sweep_environment,
                self.stats.sweep_environment_clauses,
                self.stats.kitten_solved,
            );
        }

        if self.trivially_unsat {
            return SweepOutcome::Unsat;
        }

        // Apply the proved equivalences through the existing hardened
        // substitution round: the added binaries expose the classes to
        // the SCC fold. Skipped when nothing was proved.
        if equivalences > 0 {
            if self.substitute_equivalent_literals_round() == equiv::SubstOutcome::Unsat {
                return SweepOutcome::Unsat;
            }
            if self.trivially_unsat {
                return SweepOutcome::Unsat;
            }
        }
        SweepOutcome::Ok
    }

    // ======== scheduling (kissat's intrusive ring) ========

    fn sweep_scheduled(&self, sweeper: &Sweeper, idx: u32) -> bool {
        sweeper.prev[idx as usize] != INVALID || sweeper.first == idx
    }

    fn sweep_schedule_inner(&mut self, sweeper: &mut Sweeper, idx: u32) {
        if !self.sweep_active(idx) {
            return;
        }
        let next = sweeper.next[idx as usize];
        if next != INVALID {
            // Already scheduled: unlink, then move to the tail. The
            // unlink must patch **`prev[next]`** (kissat
            // `schedule_inner`: `sweeper->prev[next] = prev`) — writing
            // `next[next]` instead leaves stale back-pointers and turns
            // the ring into a cycle, which made `unschedule_sweeping`
            // walk forever, pushing into `sweep_schedule` without bound
            // (the 6s167 OOM).
            let prev = sweeper.prev[idx as usize];
            sweeper.prev[next as usize] = prev;
            if prev == INVALID {
                sweeper.first = next;
            } else {
                sweeper.next[prev as usize] = next;
            }
            let last = sweeper.last;
            if last == INVALID {
                sweeper.first = idx;
            } else {
                sweeper.next[last as usize] = idx;
            }
            sweeper.prev[idx as usize] = last;
            sweeper.next[idx as usize] = INVALID;
            sweeper.last = idx;
        } else if sweeper.last != idx {
            let last = sweeper.last;
            if last == INVALID {
                sweeper.first = idx;
            } else {
                sweeper.next[last as usize] = idx;
            }
            sweeper.prev[idx as usize] = last;
            sweeper.next[idx as usize] = INVALID;
            sweeper.last = idx;
        }
    }

    fn sweep_schedule_outer(&mut self, sweeper: &mut Sweeper, idx: u32) {
        debug_assert!(!self.sweep_scheduled(sweeper, idx));
        debug_assert!(self.sweep_active(idx));
        let first = sweeper.first;
        if first == INVALID {
            sweeper.last = idx;
        } else {
            sweeper.prev[first as usize] = idx;
        }
        sweeper.next[idx as usize] = first;
        sweeper.prev[idx as usize] = INVALID;
        sweeper.first = idx;
    }

    /// Occurrence check for schedulability (kissat `scheduable_variable`):
    /// both polarities must occur, each within the environment clause
    /// limit. Counts only live original clauses. Returns the total
    /// occurrence count (the ranking key).
    fn sweep_occurrences(&self, idx: u32, max_occ: u64) -> Option<u64> {
        let count = |l: Lit| -> u64 {
            let mut n = 0u64;
            for (_, cid) in self.binary_graph.get(l).iter() {
                if self
                    .clauses
                    .get(*cid)
                    .is_some_and(|c| !c.deleted && !c.learned)
                {
                    n += 1;
                }
            }
            for w in self.watches.get(l) {
                if self
                    .clauses
                    .get(w.clause)
                    .is_some_and(|c| !c.deleted && !c.learned)
                {
                    n += 1;
                }
            }
            n
        };
        let pos = count(Lit::from_code(2 * idx));
        if pos == 0 || pos > max_occ {
            return None;
        }
        let neg = count(Lit::from_code(2 * idx + 1));
        if neg == 0 || neg > max_occ {
            return None;
        }
        Some(pos + neg)
    }

    // ======== environment construction ========

    /// `sweep_repr` with path compression.
    fn sweep_repr(&self, sweeper: &mut Sweeper, lit: u32) -> u32 {
        let mut prev = lit;
        let mut res = sweeper.reprs[prev as usize];
        while res != prev {
            prev = res;
            res = sweeper.reprs[prev as usize];
        }
        if res == lit {
            return res;
        }
        let not_res = res ^ 1;
        let mut prev = lit;
        loop {
            let next = sweeper.reprs[prev as usize];
            if next == res {
                break;
            }
            sweeper.reprs[(prev ^ 1) as usize] = not_res;
            sweeper.reprs[prev as usize] = res;
            prev = next;
        }
        res
    }

    /// Add a literal's variable to the environment (dedup via repr +
    /// depth stamping); kissat `add_literal_to_environment`.
    fn sweep_add_literal(&mut self, sweeper: &mut Sweeper, depth: u32, lit: u32) {
        let repr = self.sweep_repr(sweeper, lit);
        if repr != lit {
            return;
        }
        let idx = (lit >> 1) as usize;
        if sweeper.depths[idx] != 0 {
            return;
        }
        sweeper.depths[idx] = depth + 1;
        sweeper.vars.push(idx as u32);
    }

    /// Encode the scratch clause into kitten (`sweep_clause`).
    fn sweep_encode_clause(&mut self, sweeper: &mut Sweeper, depth: u32) {
        debug_assert!(sweeper.clause.len() > 1);
        // Take the scratch clause so `sweep_add_literal` can mutate the
        // sweeper while iterating; restore the (reused) buffer EMPTY —
        // the C clears the stack after every encoded clause, and
        // `sweep_binary`/`sweep_reference` push fresh literals onto an
        // empty scratch (restoring it full made every environment clause
        // a cumulative super-clause of the previous one, silently
        // destroying the equivalence structure the sweep hunts for).
        let clause = core::mem::take(&mut sweeper.clause);
        for &lit in clause.iter() {
            self.sweep_add_literal(sweeper, depth, lit);
        }
        sweeper.kitten.clause(&clause);
        sweeper.clause = clause;
        sweeper.clause.clear();
        sweeper.encoded += 1;
    }

    /// Copy a live original binary into the environment (`sweep_binary`).
    fn sweep_binary(&mut self, sweeper: &mut Sweeper, depth: u32, lit: u32, other: u32) {
        if self.sweep_repr(sweeper, lit) != lit {
            return;
        }
        if self.sweep_repr(sweeper, other) != other {
            return;
        }
        // After complete level-0 propagation an unassigned `lit` cannot
        // have a false sibling in a live binary (it would have
        // propagated); skip defensively rather than encode a falsified
        // restriction.
        if self.sweep_value(other) != 0 {
            return;
        }
        let other_depth = sweeper.depths[(other >> 1) as usize];
        let lit_depth = sweeper.depths[(lit >> 1) as usize];
        if other_depth != 0 && other_depth < lit_depth {
            return;
        }
        sweeper.clause.push(lit);
        sweeper.clause.push(other);
        self.sweep_encode_clause(sweeper, depth);
    }

    /// Copy a live original large clause into the environment, dropping
    /// level-0 false literals and retiring satisfied ones
    /// (`sweep_reference`).
    fn sweep_reference(&mut self, sweeper: &mut Sweeper, depth: u32, cid: ClauseId) {
        let Some(view) = self.clauses.get(cid) else {
            return;
        };
        if view.deleted || view.learned {
            return;
        }
        if sweeper.swept.contains(&cid) {
            return;
        }
        let lits: SmallVec<[Lit; 8]> = view.lits.iter().copied().collect();
        for &l in lits.iter() {
            let value = self.trail.lit_value(l);
            if value.is_true() {
                // Satisfied at level 0: retire from the main solver
                // (kissat `kissat_mark_clause_as_garbage`).
                self.retire_clause(cid);
                sweeper.clause.clear();
                return;
            }
            if value.is_false() {
                continue;
            }
            sweeper.clause.push(l.code());
        }
        sweeper.refs.push(cid);
        sweeper.swept.insert(cid);
        self.sweep_encode_clause(sweeper, depth);
    }

    // ======== core save / add / clear ========

    /// `save_core_clause`: filter a kitten core clause against the main
    /// solver's level-0 values and append it (INVALID-terminated) to the
    /// active core buffer. Original clauses with more than one non-false
    /// literal are ignored (they are already in the main solver).
    fn sweep_save_core_clause(&mut self, sweeper: &mut Sweeper, learned: bool, lits: &[u32]) {
        if self.trivially_unsat {
            return;
        }
        let saved = sweeper.core[sweeper.save].len();
        let mut non_false = 0u32;
        let mut skip = false;
        for &lit in lits {
            let value = self.sweep_value(lit);
            if value > 0 {
                // Satisfied lemma — nothing to extract.
                skip = true;
                break;
            }
            sweeper.core[sweeper.save].push(lit);
            if value < 0 {
                continue;
            }
            non_false += 1;
            if !learned && non_false > 1 {
                // Original clause with > 1 non-false literals: already
                // present in the main solver.
                skip = true;
                break;
            }
        }
        if skip {
            sweeper.core[sweeper.save].truncate(saved);
        } else {
            sweeper.core[sweeper.save].push(INVALID);
        }
    }

    /// Compute and save the clausal core (`save_core`).
    fn sweep_save_core(&mut self, sweeper: &mut Sweeper, core_idx: usize) {
        if self.trivially_unsat {
            return;
        }
        debug_assert!(sweeper.core[core_idx].is_empty());
        sweeper.save = core_idx;
        let mut learned = 0u64;
        sweeper.kitten.compute_clausal_core(&mut learned);
        // Collect clauses through a scratch buffer to satisfy the borrow
        // checker (traverse needs `&kitten` while `sweeper` is borrowed
        // mutably).
        let mut collected: Vec<(bool, Vec<u32>)> = Vec::new();
        sweeper
            .kitten
            .traverse_core_clauses(|learned, elits| collected.push((learned, elits.to_vec())));
        for (learned, elits) in collected {
            self.sweep_save_core_clause(sweeper, learned, &elits);
        }
    }

    /// `add_core`: re-filter the saved core against the current trail,
    /// assign units, drop larger lemmas (proof-side only in kissat),
    /// derive the empty clause when a core clause is fully falsified.
    /// Returns `false` if the formula became UNSAT.
    fn sweep_add_core(&mut self, sweeper: &mut Sweeper, core_idx: usize) -> bool {
        if self.trivially_unsat {
            return false;
        }
        let core = core::mem::take(&mut sweeper.core[core_idx]);
        let mut p = 0usize;
        while p < core.len() {
            let start = p;
            while p < core.len() && core[p] != INVALID {
                p += 1;
            }
            let clause = &core[start..p];
            p += 1; // skip the INVALID separator

            let mut satisfied = false;
            let mut unit = INVALID;
            let mut non_false = 0u32;
            for &lit in clause {
                let value = self.sweep_value(lit);
                if value > 0 {
                    satisfied = true;
                    break;
                }
                if value == 0 {
                    unit = lit;
                    non_false += 1;
                }
            }
            if satisfied {
                continue;
            }
            match non_false {
                0 => {
                    // Fully falsified on the level-0 trail: the
                    // environment (an entailed restriction) is
                    // contradictory — the main formula is UNSAT.
                    self.trivially_unsat = true;
                    return false;
                }
                1 => {
                    debug_assert!(unit != INVALID);
                    if !self.sweep_assign_unit(unit) {
                        return false;
                    }
                }
                _ => {
                    // Larger core lemma: proof-side only in kissat
                    // (CHECK_AND_ADD_LITS); proofs are gated off here,
                    // so drop it (counted).
                    self.stats.sweep_lemmas_dropped += 1;
                }
            }
        }
        true
    }

    /// Assign a sweep-derived unit at level 0 and propagate
    /// (`kissat_assign_unit` + probing propagate). Returns `false` on
    /// conflict (formula UNSAT).
    fn sweep_assign_unit(&mut self, lit: u32) -> bool {
        let l = Lit::from_code(lit);
        match self.trail.lit_value(l) {
            LBool::True => true,
            LBool::False => {
                self.trivially_unsat = true;
                false
            }
            LBool::Undef => {
                self.trail.assign_decision(l);
                self.stats.sweep_units += 1;
                if self.propagate().is_some() {
                    self.trivially_unsat = true;
                    return false;
                }
                true
            }
        }
    }

    // ======== backbone / partition refinement ========

    /// Seed the candidate lists from a SAT witness
    /// (`init_backbone_and_partition`).
    fn sweep_init_candidates(&mut self, sweeper: &mut Sweeper) {
        let vars = core::mem::take(&mut sweeper.vars);
        for &idx in vars.iter() {
            if !self.sweep_active(idx) {
                continue;
            }
            let lit = 2 * idx;
            let not_lit = lit ^ 1;
            let tmp = sweeper.kitten.value(lit);
            let candidate = if tmp < 0 { not_lit } else { lit };
            sweeper.backbone.push(candidate);
            sweeper.partition.push(candidate);
        }
        sweeper.vars = vars;
        sweeper.partition.push(INVALID);
    }

    /// Refine the partition against a new kitten model
    /// (`sweep_refine_partition`): each class splits into its
    /// model-true and model-false members; singleton sides are dropped.
    fn sweep_refine_partition(&mut self, sweeper: &mut Sweeper) {
        let old = core::mem::take(&mut sweeper.partition);
        let mut new_partition: Vec<u32> = Vec::with_capacity(old.len());
        let mut p = 0usize;
        while p < old.len() {
            let start = p;
            while p < old.len() && old[p] != INVALID {
                p += 1;
            }
            let end = p;
            p += 1; // separator

            let mut assigned_true = 0u32;
            for &other in &old[start..end] {
                if self.sweep_repr(sweeper, other) != other {
                    continue;
                }
                if self.sweep_value(other) != 0 {
                    continue;
                }
                let value = sweeper.kitten.value(other);
                if value > 0 {
                    new_partition.push(other);
                    assigned_true += 1;
                }
            }
            if assigned_true == 1 {
                new_partition.pop();
            } else if assigned_true > 1 {
                new_partition.push(INVALID);
            }

            let mut assigned_false = 0u32;
            for &other in &old[start..end] {
                if self.sweep_repr(sweeper, other) != other {
                    continue;
                }
                if self.sweep_value(other) != 0 {
                    continue;
                }
                let value = sweeper.kitten.value(other);
                if value < 0 {
                    new_partition.push(other);
                    assigned_false += 1;
                }
            }
            if assigned_false == 1 {
                new_partition.pop();
            } else if assigned_false > 1 {
                new_partition.push(INVALID);
            }
        }
        sweeper.partition = new_partition;
    }

    /// Refine the backbone candidates against a new kitten model
    /// (`sweep_refine_backbone`).
    fn sweep_refine_backbone(&mut self, sweeper: &mut Sweeper) {
        let old = core::mem::take(&mut sweeper.backbone);
        let mut kept: Vec<u32> = Vec::with_capacity(old.len());
        for lit in old {
            if self.sweep_value(lit) != 0 {
                continue;
            }
            let value = sweeper.kitten.value(lit);
            if value >= 0 {
                kept.push(lit);
            }
        }
        sweeper.backbone = kept;
    }

    fn sweep_refine(&mut self, sweeper: &mut Sweeper) {
        if !sweeper.backbone.is_empty() {
            self.sweep_refine_backbone(sweeper);
        }
        if !sweeper.partition.is_empty() {
            self.sweep_refine_partition(sweeper);
        }
    }

    /// Flip-driven shrinking of the backbone list
    /// (`flip_backbone_literals`), bounded by `sweepfliprounds`.
    fn sweep_flip_backbone(&mut self, sweeper: &mut Sweeper) {
        if SWEEP_FLIP_ROUNDS == 0 || sweeper.kitten.status() != 10 {
            return;
        }
        let mut round = 0;
        loop {
            round += 1;
            let old = core::mem::take(&mut sweeper.backbone);
            let mut kept: Vec<u32> = Vec::with_capacity(old.len());
            let mut flipped = 0u32;
            for lit in old {
                self.stats.sweep_flip_backbone += 1;
                if sweeper.kitten.flip_literal(lit) {
                    self.stats.sweep_flipped_backbone += 1;
                    flipped += 1;
                } else {
                    kept.push(lit);
                }
            }
            sweeper.backbone = kept;
            if sweeper.kitten.stats.ticks >= sweeper.limit.ticks {
                break;
            }
            if flipped == 0 || round >= SWEEP_FLIP_ROUNDS {
                break;
            }
        }
    }

    /// Flip-driven shrinking of the partition
    /// (`flip_partition_literals`); classes reduced below two members
    /// are dropped entirely (kissat semantics).
    fn sweep_flip_partition(&mut self, sweeper: &mut Sweeper) {
        if SWEEP_FLIP_ROUNDS == 0 || sweeper.kitten.status() != 10 {
            return;
        }
        let mut round = 0;
        loop {
            round += 1;
            let old = core::mem::take(&mut sweeper.partition);
            let mut kept: Vec<u32> = Vec::with_capacity(old.len());
            let mut flipped = 0u32;
            let mut src = 0usize;
            while src < old.len() {
                let start = src;
                while src < old.len() && old[src] != INVALID {
                    src += 1;
                }
                let members = src - start;
                src += 1; // separator
                debug_assert!(members > 1);
                let mut size = members as u32;
                let before = kept.len();
                for &lit in &old[start..start + members] {
                    if sweeper.kitten.flip_literal(lit) {
                        self.stats.sweep_flipped_equivalences += 1;
                        flipped += 1;
                        size -= 1;
                        if size < 2 {
                            break;
                        }
                    } else {
                        kept.push(lit);
                    }
                }
                if size > 1 {
                    kept.push(INVALID);
                } else {
                    // Class dropped: discard any members kept so far.
                    kept.truncate(before);
                }
            }
            sweeper.partition = kept;
            if sweeper.kitten.stats.ticks >= sweeper.limit.ticks {
                break;
            }
            if flipped == 0 || round >= SWEEP_FLIP_ROUNDS {
                break;
            }
        }
    }

    /// Test one backbone candidate (`sweep_backbone_candidate`).
    /// Returns `true` if the candidate was decided (unit proved or UNSAT
    /// derived).
    fn sweep_backbone_candidate(&mut self, sweeper: &mut Sweeper, lit: u32) -> bool {
        let value = sweeper.kitten.fixed(lit);
        if value != 0 {
            self.stats.sweep_fixed_backbone += 1;
            return false;
        }

        self.stats.sweep_flip_backbone += 1;
        if sweeper.kitten.status() == 10 && sweeper.kitten.flip_literal(lit) {
            self.stats.sweep_flipped_backbone += 1;
            return false;
        }

        // Assume ¬lit: UNSAT ⇒ lit is a backbone unit.
        sweeper.kitten.assume(lit ^ 1);
        let res = self.sweep_solve(sweeper);
        match res {
            KittenResult::Satisfied => {
                self.sweep_refine(sweeper);
                self.stats.sweep_sat_backbone += 1;
                false
            }
            KittenResult::Inconsistent => {
                self.stats.sweep_unsat_backbone += 1;
                // save_add_clear_core: extract + apply the units.
                self.sweep_save_core(sweeper, 0);
                let ok = self.sweep_add_core(sweeper, 0);
                sweeper.core[0].clear();
                ok
            }
            KittenResult::Unknown => {
                self.stats.sweep_unknown_backbone += 1;
                false
            }
        }
    }

    /// Test one equivalence candidate pair (`sweep_equivalence_candidates`).
    /// Returns `true` if the equivalence was proved (and its binaries
    /// applied).
    fn sweep_equivalence_candidates(
        &mut self,
        sweeper: &mut Sweeper,
        lit: u32,
        other: u32,
    ) -> bool {
        // Layout guard: the popped pair must be real literals, never the
        // `INVALID` class separator (a malformed partition would feed a
        // sentinel code into kitten and resize its import table by
        // gigabytes — defensive, the layout is maintained above).
        if lit == INVALID || other == INVALID {
            debug_assert!(false, "partition pair contained the INVALID separator");
            return false;
        }
        let not_other = other ^ 1;
        let not_lit = lit ^ 1;

        // Flip attempts first (model surgery instead of a solve). A
        // successful flip removes the candidate from its class.
        if sweeper.kitten.status() == 10 {
            if sweeper.kitten.flip_literal(lit) {
                self.stats.sweep_flip_equivalences += 1;
                self.stats.sweep_flipped_equivalences += 1;
                self.sweep_partition_pop_pair(sweeper, lit);
                return false;
            }
            if sweeper.kitten.flip_literal(other) {
                self.stats.sweep_flip_equivalences += 2;
                self.stats.sweep_flipped_equivalences += 1;
                self.sweep_partition_pop_pair(sweeper, other);
                return false;
            }
            self.stats.sweep_flip_equivalences += 2;
        }

        // First implication: ¬lit ∧ other must be unsat (other → lit).
        sweeper.kitten.assume(not_lit);
        sweeper.kitten.assume(other);
        match self.sweep_solve(sweeper) {
            KittenResult::Satisfied => {
                self.stats.sweep_sat_equivalences += 1;
                self.sweep_refine(sweeper);
                return false;
            }
            KittenResult::Unknown => {
                self.stats.sweep_unknown_equivalences += 1;
                return false;
            }
            KittenResult::Inconsistent => {
                self.stats.sweep_unsat_equivalences += 1;
            }
        }

        self.sweep_save_core(sweeper, 0);

        // Second implication: lit ∧ ¬other must be unsat (lit → other).
        sweeper.kitten.assume(lit);
        sweeper.kitten.assume(not_other);
        match self.sweep_solve(sweeper) {
            KittenResult::Satisfied => {
                self.stats.sweep_sat_equivalences += 1;
                self.sweep_refine(sweeper);
                sweeper.core[0].clear();
                return false;
            }
            KittenResult::Unknown => {
                self.stats.sweep_unknown_equivalences += 1;
                sweeper.core[0].clear();
                return false;
            }
            KittenResult::Inconsistent => {
                self.stats.sweep_unsat_equivalences += 1;
            }
        }

        self.sweep_save_core(sweeper, 1);

        // Equivalence proved: extract any units from the cores, add the
        // two entailed binaries, record the representative.
        self.stats.sweep_equivalences += 1;
        if !self.sweep_add_core(sweeper, 0) {
            return true;
        }
        if !self.sweep_add_clause_binary(lit, not_other) {
            sweeper.core[1].clear();
            return true;
        }
        sweeper.core[0].clear();

        if !self.sweep_add_core(sweeper, 1) {
            return true;
        }
        if !self.sweep_add_clause_binary(not_lit, other) {
            sweeper.core[1].clear();
            return true;
        }
        sweeper.core[1].clear();

        let (repr, eliminated) = if lit < other {
            (lit, other)
        } else {
            (other, lit)
        };
        sweeper.reprs[eliminated as usize] = repr;
        sweeper.reprs[(eliminated ^ 1) as usize] = repr ^ 1;
        self.sweep_partition_remove(sweeper, eliminated);
        self.sweep_schedule_inner(sweeper, repr >> 1);
        true
    }

    /// Add one entailed binary through the hardened `add_clause` path.
    /// Returns `false` if the formula became UNSAT.
    fn sweep_add_clause_binary(&mut self, a: u32, b: u32) -> bool {
        let la = Lit::from_code(a);
        let lb = Lit::from_code(b);
        self.add_clause([la, lb]);
        !self.trivially_unsat
    }

    /// `sweep_remove`: take the non-representative out of its partition
    /// class; a class reduced to one member is squashed entirely.
    fn sweep_partition_remove(&mut self, sweeper: &mut Sweeper, lit: u32) {
        let partition = &mut sweeper.partition;
        let Some(p) = partition.iter().position(|&l| l == lit) else {
            return;
        };
        let mut begin_class = p;
        while begin_class > 0 && partition[begin_class - 1] != INVALID {
            begin_class -= 1;
        }
        let mut end_class = p;
        while end_class < partition.len() && partition[end_class] != INVALID {
            end_class += 1;
        }
        let size = end_class - begin_class;
        debug_assert!(size > 1);
        if size == 2 {
            // Squash the whole class INCLUDING its trailing separator
            // (the C copies `end_class + 1 ..` down over `begin_class`,
            // which consumes the separator at `end_class`). Draining only
            // the literals left a doubled separator, and the next pair-pop
            // then fed the `INVALID` sentinel into `kitten.assume` —
            // importing a "variable" at index u32::MAX/2 resized the
            // import table by gigabytes (the 6s167 RSS sawtooth).
            partition.drain(begin_class..=end_class);
        } else {
            partition.remove(p);
        }
    }

    /// The equivalence test consumed the tail pair of the partition
    /// (C's `end[-3]`, `end[-2]`); a successful flip removes the flipped
    /// member, squashing a pair-only class (the C's inline trim).
    fn sweep_partition_pop_pair(&mut self, sweeper: &mut Sweeper, flipped: u32) {
        let partition = &mut sweeper.partition;
        let len = partition.len();
        if len < 3 || partition[len - 1] != INVALID {
            return;
        }
        let lit = partition[len - 3];
        let other = partition[len - 2];
        let pair_only_class = len < 4 || partition[len - 4] == INVALID;
        let _ = flipped;
        if pair_only_class {
            partition.truncate(len - 3);
        } else {
            // Class had ≥ 3 members: keep the unflipped member in place
            // and terminate the class one slot earlier.
            let retained = if lit == flipped { other } else { lit };
            partition[len - 3] = retained;
            partition[len - 2] = INVALID;
            partition.truncate(len - 1);
        }
    }

    /// One kitten solve with phase randomization (`sweep_solve`).
    fn sweep_solve(&mut self, sweeper: &mut Sweeper) -> KittenResult {
        sweeper.kitten.randomize_phases();
        self.stats.sweep_solved += 1;
        let res = sweeper.kitten.solve();
        match res {
            KittenResult::Satisfied => self.stats.sweep_sat += 1,
            KittenResult::Inconsistent => self.stats.sweep_unsat += 1,
            KittenResult::Unknown => {}
        }
        res
    }

    /// The environment itself is contradictory: extract the core; the
    /// empty clause surfaces through `sweep_add_core` (`sweep_empty_clause`).
    fn sweep_empty_clause(&mut self, sweeper: &mut Sweeper) {
        debug_assert!(!self.trivially_unsat);
        self.sweep_save_core(sweeper, 0);
        let _ = self.sweep_add_core(sweeper, 0);
        sweeper.core[0].clear();
    }

    /// Sweep one variable end-to-end (`sweep_variable`): build the
    /// environment, solve it, then run the backbone and partition loops
    /// under the shared tick budget.
    fn sweep_one_variable(&mut self, sweeper: &mut Sweeper, idx: u32) {
        if !self.sweep_active(idx) {
            return;
        }
        let start = 2 * idx;
        if sweeper.reprs[start as usize] != start {
            return; // non-representative
        }
        debug_assert!(sweeper.vars.is_empty());
        debug_assert!(sweeper.refs.is_empty());
        debug_assert!(sweeper.backbone.is_empty());
        debug_assert!(sweeper.partition.is_empty());
        debug_assert!(sweeper.encoded == 0);

        if self.sweep_value(start) != 0 {
            return; // assigned since scheduling
        }

        self.stats.sweep_variables += 1;

        // ======== environment construction (depth-limited BFS) ========
        self.sweep_add_literal(sweeper, 0, start);
        let mut expand: usize = 0;
        let mut next: usize = 1;
        let mut depth: u32 = 1;
        'environment: loop {
            if sweeper.encoded as u64 >= sweeper.limit.clauses {
                break; // environment clause limit reached
            }
            if expand == next {
                if depth as u64 >= sweeper.limit.depth {
                    break;
                }
                next = sweeper.vars.len();
                if expand == next {
                    break; // cone fully copied
                }
                depth += 1;
            }
            let vidx = sweeper.vars[expand];
            expand += 1;
            for sign in 0..2u32 {
                let lit = 2 * vidx + sign;
                let key = Lit::from_code(lit ^ 1);
                // Binary clauses containing `lit`: BIG edges out of ¬lit,
                // originals only.
                let edges: Vec<(u32, ClauseId)> = self
                    .binary_graph
                    .get(key)
                    .iter()
                    .filter(|&(_, cid)| {
                        self.clauses
                            .get(*cid)
                            .is_some_and(|c| !c.deleted && !c.learned)
                    })
                    .map(|&(other, cid)| (other.code(), cid))
                    .collect();
                for (other, _cid) in edges {
                    self.sweep_binary(sweeper, depth, lit, other);
                    if sweeper.vars.len() as u64 >= sweeper.limit.vars {
                        // environment variable limit reached
                        break 'environment;
                    }
                }
                // Large original clauses containing `lit`.
                let watchers: Vec<ClauseId> =
                    self.watches.get(key).iter().map(|w| w.clause).collect();
                for cid in watchers {
                    self.sweep_reference(sweeper, depth, cid);
                    if sweeper.vars.len() as u64 >= sweeper.limit.vars {
                        // environment variable limit reached
                        break 'environment;
                    }
                }
            }
        }
        self.stats.sweep_depth = self.stats.sweep_depth.saturating_add(depth as u64);
        self.stats.sweep_environment = self
            .stats
            .sweep_environment
            .saturating_add(sweeper.vars.len() as u64);
        self.stats.sweep_environment_clauses = self
            .stats
            .sweep_environment_clauses
            .saturating_add(sweeper.encoded as u64);

        match self.sweep_solve(sweeper) {
            KittenResult::Satisfied => {
                self.sweep_init_candidates(sweeper);
                // ======== backbone loop ========
                while !sweeper.backbone.is_empty() {
                    if self.trivially_unsat || sweeper.kitten.stats.ticks >= sweeper.limit.ticks {
                        break;
                    }
                    self.sweep_flip_backbone(sweeper);
                    if sweeper.kitten.stats.ticks >= sweeper.limit.ticks {
                        break;
                    }
                    let Some(lit) = sweeper.backbone.pop() else {
                        break;
                    };
                    if !self.sweep_active(lit >> 1) {
                        continue;
                    }
                    self.sweep_backbone_candidate(sweeper, lit);
                    if self.trivially_unsat {
                        break;
                    }
                }
                // ======== partition loop ========
                while !sweeper.partition.is_empty() && !self.trivially_unsat {
                    if sweeper.kitten.stats.ticks >= sweeper.limit.ticks {
                        break;
                    }
                    self.sweep_flip_partition(sweeper);
                    if sweeper.kitten.stats.ticks >= sweeper.limit.ticks {
                        break;
                    }
                    if sweeper.partition.is_empty() {
                        break;
                    }
                    if sweeper.partition.len() > 2 {
                        let len = sweeper.partition.len();
                        debug_assert!(sweeper.partition[len - 1] == INVALID);
                        let lit = sweeper.partition[len - 3];
                        let other = sweeper.partition[len - 2];
                        self.sweep_equivalence_candidates(sweeper, lit, other);
                    } else {
                        sweeper.partition.clear();
                    }
                }
            }
            KittenResult::Inconsistent => {
                self.sweep_empty_clause(sweeper);
            }
            KittenResult::Unknown => {}
        }

        // ======== per-variable cleanup (`clear_sweeper`) ========
        sweeper.kitten.clear();
        sweeper.kitten.track_antecedents();
        for &vidx in sweeper.vars.iter() {
            sweeper.depths[vidx as usize] = 0;
        }
        sweeper.vars.clear();
        sweeper.refs.clear();
        sweeper.swept.clear();
        sweeper.backbone.clear();
        sweeper.partition.clear();
        sweeper.encoded = 0;

        // Root-level propagation after the variable's assignments
        // (kissat dense-propagates here; every unit was propagated as it
        // was assigned, so this is a no-op unless retire/assign paths
        // queued work).
        if !self.trivially_unsat
            && self.trail.has_pending_propagation()
            && self.propagate().is_some()
        {
            self.trivially_unsat = true;
        }
    }

    /// Number of active variables still flagged for sweeping
    /// (`incomplete_variables`).
    fn sweep_incomplete_variables(&self) -> u32 {
        let mut res = 0;
        for idx in 0..self.num_vars as u32 {
            if !self.sweep_active(idx) {
                continue;
            }
            if self
                .sweep_incomplete_flags
                .get(idx as usize)
                .copied()
                .unwrap_or(false)
            {
                res += 1;
            }
        }
        res
    }
}

impl Sweeper {
    /// Initialize the sweeper (`init_sweeper`): identity reprs, empty
    /// ring, per-round limits from `sweep_completed`, fresh kitten with
    /// antecedent tracking, and the round tick budget from the effort
    /// window.
    fn new(solver: &Solver, window: u64) -> Self {
        let num_vars = solver.num_vars;
        let num_lits = num_vars * 2;
        let mut reprs = Vec::with_capacity(num_lits);
        for code in 0..num_lits as u32 {
            reprs.push(code);
        }

        // Limits grow with completed sweeps (kissat `sweep_completed`
        // doubling), capped.
        let completed = solver.sweep_completed.min(32) as u64;
        let vars_limit = (SWEEP_VARS << completed).min(SWEEP_MAX_VARS);
        let depth_limit = (SWEEP_DEPTH + completed).min(SWEEP_MAX_DEPTH);
        let clause_limit = (SWEEP_CLAUSES << completed).min(SWEEP_MAX_CLAUSES);

        // Effort budget: per-mille of the round window (kissat
        // `SET_EFFORT_LIMIT(sweep, kitten_ticks)` over the search-work
        // reference; ours is the inprocessing round's propagation
        // window, floored at kissat's `mineffort`).
        let reference = window.max(SWEEP_MIN_EFFORT);
        let effort_permille = crate::kitten_sweep_effort_permille();
        let budget = ((reference / 1000) * effort_permille).max(1);

        let mut kitten = Kitten::new();
        kitten.track_antecedents();
        kitten.set_ticks_limit_delta(budget);

        Self {
            depths: vec![0; num_vars],
            reprs,
            next: vec![INVALID; num_vars],
            prev: vec![INVALID; num_vars],
            first: INVALID,
            last: INVALID,
            vars: Vec::new(),
            refs: Vec::new(),
            swept: rustc_hash::FxHashSet::default(),
            clause: Vec::new(),
            backbone: Vec::new(),
            partition: Vec::new(),
            core: [Vec::new(), Vec::new()],
            save: 0,
            encoded: 0,
            kitten,
            limit: SweepLimits {
                ticks: budget,
                clauses: clause_limit,
                depth: depth_limit,
                vars: vars_limit,
            },
        }
    }

    /// Count active variables whose representative differs from
    /// themselves (`release_sweeper`'s merged count); drops the sweeper.
    fn release(self, solver: &Solver) -> u32 {
        let mut merged = 0;
        for idx in 0..solver.num_vars as u32 {
            if !solver.sweep_active(idx) {
                continue;
            }
            let lit = 2 * idx;
            if self.reprs[lit as usize] != lit {
                merged += 1;
            }
        }
        merged
    }

    // ======== scheduling ========

    fn next_scheduled(&mut self) -> Option<u32> {
        let res = self.last;
        if res == INVALID {
            return None;
        }
        let prev = self.prev[res as usize];
        self.prev[res as usize] = INVALID;
        if prev == INVALID {
            self.first = INVALID;
        } else {
            self.next[prev as usize] = INVALID;
        }
        self.last = prev;
        Some(res)
    }

    /// `schedule_sweeping`: reschedule the previously-remaining vars,
    /// then schedule every other schedulable var, ranked by total
    /// occurrences (ascending; the matched null scrambles this ranking).
    /// Returns the scheduled count.
    fn schedule_sweeping(&mut self, solver: &mut Solver) -> u32 {
        // `reschedule_previously_remaining`
        let remaining = core::mem::take(&mut solver.sweep_schedule);
        let mut rescheduled = 0u32;
        for idx in remaining {
            if !solver.sweep_active(idx) {
                continue;
            }
            if solver.sweep_scheduled(self, idx) {
                continue;
            }
            match solver.sweep_occurrences(idx, self.limit.clauses) {
                Some(_) => {
                    solver.sweep_schedule_inner(self, idx);
                    rescheduled += 1;
                }
                None => {
                    if (idx as usize) < solver.sweep_incomplete_flags.len() {
                        solver.sweep_incomplete_flags[idx as usize] = false;
                    }
                }
            }
        }

        // `schedule_all_other_not_scheduled_yet`
        let mut fresh: Vec<(u64, u32)> = Vec::new();
        for idx in 0..solver.num_vars as u32 {
            if !solver.sweep_active(idx) {
                continue;
            }
            let flagged = solver
                .sweep_incomplete_flags
                .get(idx as usize)
                .copied()
                .unwrap_or(false);
            if solver.sweep_incomplete && !flagged {
                continue;
            }
            if solver.sweep_scheduled(self, idx) {
                continue;
            }
            match solver.sweep_occurrences(idx, self.limit.clauses) {
                Some(occ) => fresh.push((occ, idx)),
                None => {
                    if (idx as usize) < solver.sweep_incomplete_flags.len() {
                        solver.sweep_incomplete_flags[idx as usize] = false;
                    }
                }
            }
        }
        // Rank ascending (kissat RADIX_STACK). The matched null
        // scrambles the ranking key deterministically: same candidate
        // set, same filters, different order.
        if crate::kitten_sweep_null_enabled() {
            fresh.sort_by_key(|&(_, idx)| {
                (idx.wrapping_mul(0x9E37_79B1).rotate_left(13)) ^ (idx >> 3)
            });
        } else {
            fresh.sort_by_key(|&(occ, _)| occ);
        }
        for &(_, idx) in &fresh {
            solver.sweep_schedule_outer(self, idx);
        }

        let scheduled = fresh.len() as u32 + rescheduled;
        // Incomplete accounting: if no scheduled var remains flagged,
        // the previous round completed — bump `sweep_completed` and
        // re-mark this round's scheduled set.
        let incomplete = solver.sweep_incomplete_variables();
        if incomplete == 0 {
            if solver.sweep_incomplete {
                solver.sweep_completed += 1;
            }
            self.mark_incomplete(solver);
        }
        scheduled
    }

    /// Flag every currently scheduled variable as incomplete
    /// (`mark_incomplete`).
    fn mark_incomplete(&mut self, solver: &mut Solver) {
        if solver.sweep_incomplete_flags.len() < solver.num_vars {
            solver.sweep_incomplete_flags.resize(solver.num_vars, false);
        }
        let mut idx = self.first;
        while idx != INVALID {
            solver.sweep_incomplete_flags[idx as usize] = true;
            idx = self.next[idx as usize];
        }
        solver.sweep_incomplete = true;
    }

    /// `unschedule_sweeping`: retain the untried scheduled variables for
    /// the next round; if nothing is left incomplete, the sweep counts
    /// as completed.
    fn unschedule_sweeping(&mut self, solver: &mut Solver, swept: u64, scheduled: u32) {
        let mut idx = self.first;
        while idx != INVALID {
            if solver.sweep_active(idx) {
                solver.sweep_schedule.push(idx);
            }
            idx = self.next[idx as usize];
        }
        let incomplete = solver.sweep_incomplete_variables();
        if incomplete == 0 {
            solver.sweep_incomplete = false;
            solver.sweep_completed += 1;
        }
        let _ = (swept, scheduled);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Occurrence counting sanity: both polarity keys must see the
    /// binary clauses of a two-var equivalence.
    #[test]
    fn sweep_occurrences_counts_both_polarities() {
        let mut s = Solver::new();
        for _ in 0..4 {
            let _ = s.new_var();
        }
        s.add_clause_dimacs(&[-1, 2]);
        s.add_clause_dimacs(&[1, -2]);
        let occ = s.sweep_occurrences(0, 1024);
        assert_eq!(occ, Some(2));
    }
}
