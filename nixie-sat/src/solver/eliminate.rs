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

/// Occurrence lists for one elimination round: a CSR primary plus a
/// per-literal overflow.
///
/// The historical `Vec<Vec<ClauseId>>` shape paid its capacity in glibc heap
/// bins: ~28 M occurrences on worker-class instances is ~111 MB of ~600 B
/// chunks, and every byte freed at round end stays resident in bin memory
/// forever (measured: the ~180 MB gap between live search structures and
/// the actual RSS floor). The CSR primary is one exact-size `Vec` — an
/// mmap-scale allocation the allocator returns on drop — while mid-round
/// additions (resolvents connecting as they are learned) go to lazily
/// allocated per-literal overflow `Vec`s, which stay tiny relative to the
/// primary. The combined view (primary span, then overflow) has exactly the
/// contents and order of the historical single `Vec`, so every consumer
/// below is trajectory-neutral by construction.
struct RoundOccs {
    /// CSR data: literal `code`'s primary span is
    /// `primary[span_end[code-1]..span_end[code]]` (`[..0]` for `code == 0`).
    primary: Vec<u32>,
    /// Exclusive end offset of each literal's primary span.
    span_end: Vec<u32>,
    /// Live length of each literal's primary span (`<=` the span extent;
    /// shrunk by flushes/clears, never regrows — additions go to `extra`).
    prim_len: Vec<u32>,
    /// Per-literal overflow for mid-round additions, in arrival order.
    extra: Vec<Vec<u32>>,
}

impl RoundOccs {
    /// Empty lists for `n` literal codes.
    fn new(n: usize) -> Self {
        Self {
            primary: Vec::new(),
            span_end: vec![0; n],
            prim_len: vec![0; n],
            extra: vec![Vec::new(); n],
        }
    }

    /// Seed the CSR layout from per-literal occurrence counts (the counting
    /// pass of `elim_round`): fixes every span's extent so the connect pass
    /// can fill `primary` exactly, with no per-literal doubling growth.
    fn layout(&mut self, counts: &[u32]) {
        let mut acc = 0u32;
        for (end, &n) in self.span_end.iter_mut().zip(counts.iter()) {
            acc = acc.saturating_add(n);
            *end = acc;
        }
        self.primary = vec![0; acc as usize];
        // `prim_len` stays 0 here and doubles as the fill cursor: `connect`
        // writes at `span_start + prim_len` and advances it, so it reaches
        // the span's extent exactly when the connect pass completes (any
        // reader between layout and connect sees empty lists, matching a
        // fresh `Vec::new()` per literal).
    }

    /// Append `cid` to literal `code`'s primary span (connect pass only,
    /// while spans still have room — mid-round additions use `push`).
    #[inline]
    fn connect(&mut self, code: usize, cid: ClauseId) {
        let at = code_span_start(&self.span_end, code) + self.prim_len[code] as usize;
        self.primary[at] = cid.0;
        self.prim_len[code] += 1;
    }

    /// Combined-view length of literal `code`'s list.
    #[inline]
    fn len(&self, code: usize) -> usize {
        self.prim_len[code] as usize + self.extra[code].len()
    }

    /// Append `cid` to literal `code`'s overflow (mid-round additions).
    #[inline]
    fn push(&mut self, code: usize, cid: ClauseId) {
        self.extra[code].push(cid.0);
    }

    /// Literal `code`'s list as one owned `Vec`, primary-then-overflow —
    /// exactly the historical `Vec<ClauseId>` contents and order.
    fn combined(&self, code: usize) -> Vec<ClauseId> {
        let start = code_span_start(&self.span_end, code);
        let pl = self.prim_len[code] as usize;
        let mut v = Vec::with_capacity(pl + self.extra[code].len());
        v.extend(self.primary[start..start + pl].iter().map(|&r| ClauseId(r)));
        v.extend(self.extra[code].iter().map(|&r| ClauseId(r)));
        v
    }

    /// Position of `cid` in literal `code`'s combined view, if present.
    fn position(&self, code: usize, cid: ClauseId) -> Option<usize> {
        let start = code_span_start(&self.span_end, code);
        let pl = self.prim_len[code] as usize;
        self.primary[start..start + pl]
            .iter()
            .position(|&r| r == cid.0)
            .or_else(|| {
                self.extra[code]
                    .iter()
                    .position(|&r| r == cid.0)
                    .map(|p| p + pl)
            })
    }

    /// `Vec::swap_remove` semantics over the combined view: move the last
    /// combined element into `pos`, dropping the previous occupant.
    fn swap_remove(&mut self, code: usize, pos: usize) {
        let pl = self.prim_len[code] as usize;
        if let Some(last) = self.extra[code].pop() {
            // The combined tail lives in the overflow: it fills the hole,
            // wherever the hole sits.
            if pos < pl {
                let start = code_span_start(&self.span_end, code);
                self.primary[start + pos] = last;
            } else {
                let epos = pos - pl;
                if epos < self.extra[code].len() {
                    self.extra[code][epos] = last;
                }
                // else `pos` addressed the popped slot itself — nothing to
                // fill.
            }
        } else {
            // Overflow empty: the combined tail closes the primary span.
            let start = code_span_start(&self.span_end, code);
            self.prim_len[code] -= 1;
            if pos + 1 < pl {
                self.primary[start + pos] = self.primary[start + pl - 1];
            }
        }
    }

    /// Empty literal `code`'s list (the span's bytes stay but are unread).
    #[inline]
    fn clear(&mut self, code: usize) {
        self.prim_len[code] = 0;
        self.extra[code].clear();
    }

    /// Rewrite literal `code`'s list from `lits` (the flush-sort result:
    /// filtered and ordered). Splits back into primary span then overflow,
    /// preserving the combined order; `lits.len()` never exceeds the
    /// combined length a flush started from.
    fn rewrite(&mut self, code: usize, lits: &[ClauseId]) {
        let start = code_span_start(&self.span_end, code);
        let extent = self.span_end[code] as usize - start;
        let head = lits.len().min(extent);
        for (i, &cid) in lits.iter().take(head).enumerate() {
            self.primary[start + i] = cid.0;
        }
        self.prim_len[code] = head as u32;
        self.extra[code].clear();
        self.extra[code].extend(lits[head..].iter().map(|&c| c.0));
    }

    /// Iterate literal `code`'s combined view, primary then overflow.
    fn iter(&self, code: usize) -> impl Iterator<Item = ClauseId> + '_ {
        let start = code_span_start(&self.span_end, code);
        let pl = self.prim_len[code] as usize;
        self.primary[start..start + pl]
            .iter()
            .chain(self.extra[code].iter())
            .map(|&r| ClauseId(r))
    }
}

/// Start offset of literal `code`'s primary span.
#[inline]
fn code_span_start(span_end: &[u32], code: usize) -> usize {
    if code == 0 {
        0
    } else {
        span_end[code - 1] as usize
    }
}

/// Per-phase scratch state for the eliminator. Only alive during an
/// elimination phase; `occs`/`noccs`/`val`/`mark` are indexed by literal code.
struct Eliminator {
    /// Occurrence lists over original clauses, connected on every literal
    /// (level-0-falsified entries included; the `val` checks filter them, as
    /// in cadical). Deletion is lazy – dead ids are skipped on access and
    /// compacted by [`Solver::elim_flush_sort_occs`].
    occs: RoundOccs,
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
    /// Scratch for [`Solver::elim_flush_sort_occs`]'s decorated sort,
    /// reused across every occurrence-list flush of the round (the
    /// per-call `Vec` collect measured 6.2 % of instructions on
    /// elimination-heavy circuit instances – one malloc + copy per
    /// scheduled variable, twice).
    occ_scratch: Vec<(usize, ClauseId)>,
    /// Scratch for the flush's sorted keep-list, reused across every flush
    /// (the per-flush `Vec<ClauseId>` collect was pure allocation churn on
    /// elimination-heavy instances).
    keep_scratch: Vec<ClauseId>,
    /// Scratch for [`Solver::elim_resolve_clauses`]'s marking phase, reused
    /// across every resolution of the round (cadical reuses its member
    /// `clause`/`marked` vectors the same way). The previous per-call
    /// SmallVecs spilled to the heap on long-antecedent resolutions and
    /// their push/grow path measured **21.5 % of the whole process** on
    /// g2-slp (8 M resolutions per phase-1 round). `res_resolvent` is only
    /// cloned into an owned clause on the rare non-tautological outcome;
    /// it also carries the marked-literal prefix `[..marked_n]` used to
    /// unmark c's literals (the separate `res_marked` vector it replaces
    /// was measured at ~4 % of g2-slp and removed).
    res_resolvent: Vec<Lit>,
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
            occs: RoundOccs::new(n),
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
            occ_scratch: Vec::new(),
            keep_scratch: Vec::new(),

            res_resolvent: Vec::new(),
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
            // Proof-attached runs are now admitted (LRAT/DRAT): every
            // mutation the round makes is emitted as a proof event —
            // resolvent additions carry the resolving pair as their RUP
            // chain (negating a resolvent falsifies both parents, so unit
            // propagation on the pair conflicts), deletions are emitted as
            // deletion lines (which need no justification in LRAT), and
            // in-place strengthens reuse `proof_strengthen_clause` when the
            // dropped literals are falsified on the *real* trail. The one
            // BVE effect that has no cheap provenance — unit and empty
            // resolvents, whose justifications depend on elimination-local
            // assignments — aborts the pivot under an attached proof
            // instead (see `elim_resolvents_bounded` / `elim_shrink_clause`),
            // so the round stays strictly weaker, never unprovable.
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
        // Proof-attached runs eliminate in both the pre-search fixpoint and
        // the mid-search schedule: every mutation carries a checker-valid
        // justification (resolvent chains lead with the units of dropped
        // level-0 literals, then the parents; deletions are justification-
        // free; refuses cover the unprovable cases — see the study).
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
        if std::env::var("NIXIE_LOG_ELIM").is_ok() {
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
        if std::env::var("NIXIE_LOG_ELIM").is_ok() {
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
            if std::env::var("NIXIE_LOG_ELIM").is_ok() {
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
        // Deferred-side-effect scan: satisfied clauses retire and
        // falsified-clause variables get marked AFTER the whole pass, so the
        // scan itself needs no `&mut self` and iterates every clause's
        // literals **in the arena** (the previous shape collected all clause
        // ids into a fresh `Vec` per round and snapshot-copied every
        // original clause's literals into a heap SmallVec – the dominant
        // allocation churn of elimination-heavy instances' profiles).
        // Equivalence: nothing in the scan reads deletion flags or the mark
        // vector (each clause is visited once, `ctx.lit_val` is a local
        // snapshot), and both deferred effects are consumed before the
        // schedule is seeded below, in the same clause-id order.
        let mut to_retire: SmallVec<[ClauseId; 64]> = SmallVec::new();
        let mut to_mark: SmallVec<[Var; 64]> = SmallVec::new();
        // Exact-capacity presize for the occurrence lists (2026-09-05):
        // the connect pass below pushes into per-literal `Vec`s whose
        // doubling growth leaves up to 2x the live occurrence volume in
        // capacity — on clause-dense instances (worker-class: ~28 M
        // occurrences, ~111 MB live) that was ~100+ MB of pure transient
        // overshoot per elimination round, half of which the allocator
        // retains after the round. This counting pass applies the *same*
        // filters the connect pass applies (same `ctx.lit_val` snapshot —
        // nothing derives new units between here and there) and presizes
        // each list to its exact final entry count, so the connect pushes
        // land at capacity and never double. Contents and per-literal
        // order are unchanged — trajectory-neutral by construction.
        {
            for cid in self.clauses.iter_ids() {
                let Some(c) = self.clauses.get(cid) else {
                    continue;
                };
                if c.deleted || c.learned || c.lits.len() < 2 {
                    continue;
                }
                if c.lits.iter().any(|&lit| ctx.lit_val(lit) == 1) {
                    continue;
                }
                for &lit in c.lits.iter() {
                    if ctx.lit_val(lit) == 0 {
                        ctx.noccs[lit.code() as usize] += 1;
                    }
                }
            }
            ctx.occs.layout(&ctx.noccs);
            for c in ctx.noccs.iter_mut() {
                *c = 0;
            }
        }
        for cid in self.clauses.iter_ids() {
            let Some(c) = self.clauses.get(cid) else {
                continue;
            };
            if c.deleted || c.learned || c.lits.len() < 2 {
                continue;
            }
            let mut satisfied = false;
            let mut falsified = false;
            for &lit in c.lits.iter() {
                match ctx.lit_val(lit) {
                    1 => satisfied = true,
                    -1 => falsified = true,
                    _ => {}
                }
            }
            if satisfied {
                to_retire.push(cid);
                continue;
            }
            if falsified {
                for &lit in c.lits.iter() {
                    if ctx.lit_val(lit) == 0 {
                        to_mark.push(lit.var());
                    }
                }
            }
            for &lit in c.lits.iter() {
                if ctx.lit_val(lit) == 0 {
                    let code = lit.code() as usize;
                    ctx.occs.connect(code, cid);
                    ctx.noccs[code] += 1;
                }
            }
        }
        for cid in to_retire {
            self.elim_retire(cid);
            self.stats.deleted_clauses += 1;
            ctx.dirty = true;
        }
        for v in to_mark {
            self.mark_elim_one(v);
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
        // Cheap gates BEFORE the flush+sort, on the raw (uncompacted) list
        // lengths – cadical's `try_to_eliminate_variable` order: it reads
        // `ps.size()`/`ns.size()` and rejects `!pos || !neg` and
        // `max > elimocclim` before `elim_resolvents_are_bounded` does any
        // flushing or sorting. Our previous order flushed+sorted both
        // occurrence lists for every scheduled variable, only to throw the
        // work away for the (majority, in later rounds) variables that fail
        // these gates. Raw lengths only over-estimate the live counts, so
        // the occ-limit gate can newly skip a variable whose *compacted*
        // count would have squeaked under the limit – a heuristic-order
        // divergence from the previous behavior, verified by verdicts
        // (corpus sweep + differential fuzz), not by trajectory identity.
        let raw_pos = ctx.occs.len(pivot.code() as usize);
        let raw_neg = ctx.occs.len(pivot.negate().code() as usize);
        if raw_pos == 0 || raw_neg == 0 {
            // Pure/one-sided variable: leave it to the pure-literal pass
            // (our model reconstruction only covers resolution
            // elimination).
            return;
        }
        if raw_pos.max(raw_neg) > ELIM_OCC_LIMIT {
            return;
        }
        self.elim_flush_sort_occs(ctx, pivot);
        self.elim_flush_sort_occs(ctx, pivot.negate());
        let mut pos = ctx.noccs[pivot.code() as usize] as usize;
        let mut neg = ctx.noccs[pivot.negate().code() as usize] as usize;
        if pos == 0 || neg == 0 {
            // All entries dead since the raw check above (retirements from
            // this round's earlier variables): same skip the flushed-count
            // order always took.
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

        let mut collected: Vec<(SmallVec<[Lit; 8]>, ClauseId, ClauseId)> = Vec::new();
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
        let code = lit.code() as usize;
        if ctx.occs.len(code) == 0 {
            return;
        }
        let clauses = &self.clauses;
        let scratch = &mut ctx.occ_scratch;
        scratch.clear();
        scratch.extend(ctx.occs.iter(code).filter_map(|cid| {
            if let Some(c) = clauses.get(cid)
                && !c.deleted
            {
                return Some((c.lits.len(), cid));
            }
            None
        }));
        scratch.sort_by_key(|&(len, _)| len);
        let kept = &mut ctx.keep_scratch;
        kept.clear();
        kept.extend(scratch.iter().copied().map(|(_, cid)| cid));
        ctx.occs.rewrite(code, kept);
        ctx.noccs[code] = ctx.occs.len(code) as u32;
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
        collected: &mut Vec<(SmallVec<[Lit; 8]>, ClauseId, ClauseId)>,
    ) -> bool {
        let bound = (pos + neg) as i64 + self.elim_bound;
        // NOTE: these clones are LOAD-BEARING, not borrow-appeasement. The
        // pair loop below mutates the live `ctx.occs[±pivot]` lists through
        // `elim_shrink_clause`'s self-subsumption path: dropping the pivot
        // from a clause physically `swap_remove`s it from `occs[pivot]`
        // (see the stale-entry false-SAT note there). A take/put-back
        // "optimization" leaves those lists empty during the loop, the
        // removal silently no-ops, and the restore reintroduces a stale
        // entry – the exact hazard class that swap_remove exists to prevent
        // (measured as a trajectory divergence on
        // `circuit_48in64…dist128_seed1` before being caught by the
        // identity gate and reverted). Do not replace the clones without
        // threading the drop-removals through the taken window.
        let ps: Vec<ClauseId> = ctx.occs.combined(pivot.code() as usize);
        let ns: Vec<ClauseId> = ctx.occs.combined(pivot.negate().code() as usize);
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
                        // LRAT unit-resolvent provenance (2026-09): the unit
                        // resolvent {u} of C(v) and D(¬v) is RUP with the
                        // resolvent shape — under ¬u every parent literal is
                        // false (dropped literals via their level-0 unit
                        // hints, u by the negation itself), C is unit on v,
                        // D is unit on ¬v → conflict. Emit the derived unit,
                        // record its id in the unit table (later chains may
                        // hint it), then apply it — full-strength BVE, no
                        // more pivot abort under proofs. A missing unit id
                        // skips derivation AND assignment (weaker, sound);
                        // a unit contradicting an earlier elim unit ends the
                        // round through `elim_assign_unit`'s contradiction
                        // arm, which seeds the empty-clause chain from the
                        // two unit ids.
                        let mut ok_to_assign = ctx.lit_val(u) != 1;
                        if ok_to_assign && self.lrat {
                            let mut chain: SmallVec<[i64; 8]> = SmallVec::new();
                            'u: for parent in [cid, nid] {
                                let Some(pv) = self.clauses.get(parent) else {
                                    continue;
                                };
                                for &lit in pv.lits {
                                    if ctx.lit_val(lit) == -1 {
                                        let uid = self
                                            .proof_unit_id_get_or_zero(lit.negate().to_dimacs());
                                        if uid == 0 {
                                            ok_to_assign = false;
                                            break 'u;
                                        }
                                        chain.push(uid);
                                    }
                                }
                            }
                            if ok_to_assign {
                                chain.push(self.proof_clause_id(cid));
                                chain.push(self.proof_clause_id(nid));
                                let pfid = self.proof_next_id();
                                if let Some(proof) = &mut self.proof {
                                    proof.add_derived_unit_clause(pfid, u.to_dimacs(), &chain);
                                }
                                self.proof_set_unit_id(u.to_dimacs(), pfid);
                            }
                        }
                        if ok_to_assign {
                            self.elim_assign_unit(ctx, u);
                        }
                        if self.trivially_unsat {
                            return false;
                        }
                    }
                    ElimResolve::Resolvent(r) => {
                        resolvents += 1;
                        if r.len() > ELIM_CLS_LIMIT || resolvents > bound {
                            return false;
                        }
                        // Record the resolving pair: the proof emission at
                        // addition time needs both parents' LRAT ids as the
                        // resolvent's RUP chain.
                        collected.push((r, cid, nid));
                    }
                }
                if ctx.lit_val(pivot) != 0 {
                    return false;
                }
                // A size-0 resolvent sets `trivially_unsat` inside
                // `elim_resolve_clauses`; retire the pair loop immediately
                // so no later pair can shrink or retire a clause whose id
                // the seeded empty-clause chain references (a deleted hint
                // is not active at replay time).
                if self.trivially_unsat {
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
        // Both buffers are Eliminator-scoped scratch, cleared per resolution
        // and reused across the round (cadical's member `clause`/`marked`);
        // per-call SmallVecs here spilled to the heap on every long-antecedent
        // resolution and dominated the whole phase.
        // (No separate marking bookkeeping is kept — cadical `unmark(c)`
        // re-derives the set from the clause; the marked literals are the
        // `res_resolvent` prefix captured as `marked_n` after the c-scan.)
        ctx.res_resolvent.clear();
        let mut s = 0usize;

        let mut t = 0usize;
        let mut tautological = false;

        // The marked prefix length, captured right after the c-scan: the
        // marked literals are exactly `res_resolvent[0..marked_n]` (the
        // d-scan only appends below it and never writes marks). Zero when
        // the c-scan broke before marking anything (missing/satisfied).
        let mut marked_n = 0usize;
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
                        let code = lit.code() as usize;
                        ctx.mark[code] = 1;
                        ctx.mark[lit.negate().code() as usize] = -1;
                        ctx.res_resolvent.push(lit);
                        s += 1;
                    }
                }
            }
            marked_n = ctx.res_resolvent.len();

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
                            ctx.res_resolvent.push(lit);
                        }
                        t += 1;
                    }
                }
            }
        }

        // ---- effect phase ----
        // Unmark inlined over the disjoint ctx fields: the marked literals
        // are `res_resolvent[0..marked_n]` (the c-scan's prefix; the d-scan
        // only appends below it and never writes marks). Clearing writes 0
        // over the +1/-1 pair set above.
        for &lit in ctx.res_resolvent[..marked_n].iter() {
            ctx.mark[lit.code() as usize] = 0;
            ctx.mark[lit.negate().code() as usize] = 0;
        }
        if missing {
            return ElimResolve::Skip;
        }
        if let Some(r) = retire {
            self.elim_retire_clause(ctx, r);
            return ElimResolve::Skip;
        }

        if tautological {
            return ElimResolve::Skip;
        }

        let size = ctx.res_resolvent.len();
        if size == 0 {
            // LRAT: with every non-pivot parent literal falsified at level
            // 0, both parents are unit on their pivot literal under those
            // units — the empty clause is RUP over `[unit ids] ++ [C, D]`.
            // Seed `lrat_chain` here (the trivially-unsat exit emits the
            // empty clause through `drat_emit_empty(None)`, which keeps a
            // non-empty chain intact); a missing unit id leaves the chain
            // empty (the verdict stays correct — search rediscovers the
            // conflict — but the proof would not verify).
            if self.lrat && self.lrat_chain.is_empty() {
                let mut ok = true;
                let mut chain: SmallVec<[i64; 8]> = SmallVec::new();
                'z: for parent in [cid, nid] {
                    let Some(pv) = self.clauses.get(parent) else {
                        continue;
                    };
                    for &lit in pv.lits {
                        if lit == pivot || lit == pivot.negate() {
                            continue;
                        }
                        let uid = self.proof_unit_id_get_or_zero(lit.negate().to_dimacs());
                        if uid == 0 {
                            ok = false;
                            break 'z;
                        }
                        chain.push(uid);
                    }
                }
                if ok {
                    chain.push(self.proof_clause_id(cid));
                    chain.push(self.proof_clause_id(nid));
                    self.lrat_chain.extend(chain.iter().copied());
                }
            }
            self.trivially_unsat = true;
            return ElimResolve::Skip;
        }
        if size == 1 {
            return ElimResolve::Unit(ctx.res_resolvent[0]);
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
        if let Some((sid, drop_lit)) = shrink
            && self.elim_shrink_clause(ctx, sid, &[drop_lit])
        {
            return ElimResolve::Skip;
        }
        // A refused shrink (proof-attached run with an unprovable in-place
        // rewrite, or a live-reason guard) still owes this pair's resolvent:
        // the self-subsumption Skip above is only equivalent to *having
        // performed* the shrink. Returning Skip without either leaves a hole
        // in the resolution closure — model reconstruction then extends a
        // partial assignment that violates a retired original (a false Sat;
        // reproduced on crn_11_99_u under weakened elimination, 2026-09-02).
        // Fall through and add the ordinary resolvent instead: exactly the
        // unoptimized form of the refused shrink.
        // The one owned allocation: only ~6 % of resolutions on
        // elimination-heavy instances produce a non-tautological resolvent.
        ElimResolve::Resolvent(ctx.res_resolvent.iter().copied().collect())
    }

    /// Add the resolvents collected by [`Self::elim_resolvents_bounded`]
    /// (cadical `elim_add_resolvents`): each non-tautological resolvent
    /// (≥ 2 literals) becomes an original clause, connected into the
    /// occurrence lists and enqueued for backward subsumption.
    fn elim_add_resolvents(
        &mut self,
        ctx: &mut Eliminator,
        collected: &[(SmallVec<[Lit; 8]>, ClauseId, ClauseId)],
    ) {
        for (r, pid, nid) in collected {
            if self.trivially_unsat {
                return;
            }
            // Satisfied resolvents are pointless (an antecedent was
            // satisfied during the scan and is being retired).
            if r.iter().any(|&l| ctx.lit_val(l) == 1) {
                continue;
            }
            // Proof emission: a resolvent R of C(v) and D(¬v) is RUP via
            // its parents — negating R falsifies every *retained* literal
            // of both parents except v/¬v, so unit propagation derives v
            // from C and ¬v from D, a conflict. The parents are retired
            // only *after* all resolvents of the pivot are added, so parent
            // hints are verifiable at addition time. The subtlety: the
            // resolvent DROPS every parent literal falsified at level 0
            // (unit-simplified away), and an LRAT checker replays each
            // addition from a fresh assignment — it does not know those
            // units. Each dropped literal's level-0 unit must therefore be
            // a hint BEFORE the parents, or the parent clause has two
            // undetermined literals and the chain fails ("hint is not
            // unit"; found on crn_11_99_u with mid-search elimination,
            // 2026-09-02). Units-first ordering: each unit hint has exactly
            // one literal, so it propagates immediately.
            let mut proof_skip = false;
            if self.proof.is_some() {
                let mut chain: SmallVec<[i64; 8]> = SmallVec::new();
                for parent in [*pid, *nid] {
                    let Some(pv) = self.clauses.get(parent) else {
                        continue;
                    };
                    for &lit in pv.lits {
                        if ctx.lit_val(lit) == -1 && !r.contains(&lit) {
                            // Falsified at level 0 and dropped from the
                            // resolvent: its unit must lead the chain.
                            let uid = self.proof_unit_id_get_or_zero(lit.negate().to_dimacs());
                            if uid == 0 {
                                // A level-0 literal without a recorded unit:
                                // impossible since the flush invariant holds
                                // (see `assert_learned_clause`), but never
                                // emit an unverifiable chain — drop this
                                // resolvent entirely (weaker elimination,
                                // sound proof).
                                proof_skip = true;
                                break;
                            }
                            chain.push(uid);
                        }
                    }
                    if proof_skip {
                        break;
                    }
                }
                if !proof_skip {
                    chain.push(self.proof_clause_id(*pid));
                    chain.push(self.proof_clause_id(*nid));
                    let dimacs: SmallVec<[i32; 8]> = r.iter().map(|l| l.to_dimacs()).collect();
                    let pfid = self.proof_next_id();
                    if let Some(proof) = &mut self.proof {
                        proof.add_derived_clause(pfid, false, &dimacs, &chain);
                    }
                    self.mark_subsume_lits(r.iter());
                    let rid = self.clauses.add_original(r.iter().copied());
                    self.proof_set_clause_id(rid, pfid);
                    for &lit in r {
                        if ctx.lit_val(lit) == 0 {
                            let code = lit.code() as usize;
                            ctx.occs.push(code, rid);
                            ctx.noccs[code] += 1;
                        }
                    }
                    ctx.backward.push(rid);
                    ctx.dirty = true;
                }
            } else {
                let rid = self.clauses.add_original(r.iter().copied());
                for &lit in r {
                    if ctx.lit_val(lit) == 0 {
                        let code = lit.code() as usize;
                        ctx.occs.push(code, rid);
                        ctx.noccs[code] += 1;
                    }
                }
                ctx.backward.push(rid);
                ctx.dirty = true;
            }
            let _ = &proof_skip;
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
            let ids: Vec<ClauseId> = ctx.occs.combined(side.code() as usize);
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
            ctx.occs.clear(side.code() as usize);
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
        // Deletion lines need no justification in LRAT (they only shrink
        // the active set the checker propagates over), so retired
        // originals are emitted unconditionally when a proof is attached.
        // Reads the clause before the flag flips.
        self.drat_delete(cid);
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
    fn elim_shrink_clause(&mut self, ctx: &mut Eliminator, cid: ClauseId, drop: &[Lit]) -> bool {
        let lits: SmallVec<[Lit; 8]> = match self.clauses.get(cid) {
            Some(c) if !c.deleted => c.lits.iter().copied().collect(),
            _ => return false,
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
                return false;
            }
        }
        let new_lits: SmallVec<[Lit; 8]> = lits
            .iter()
            .copied()
            .filter(|&l| !drop.contains(&l))
            .collect();
        // Under an attached proof, an in-place strengthen is only provable
        // when every dropped literal is falsified by a **proof-backed**
        // level-0 unit (one recorded in the LRAT unit table): the checker
        // derives the shorter clause by propagating those units. Trail
        // falsifiers without a proof unit (e.g. lucky-phase decisions) and
        // elimination-local falsifiers are not proof-active, and
        // unit/empty strengthenings have the same provenance problem as
        // unit resolvents. Abort the strengthen in those cases — the
        // clause keeps its literals, strictly weaker, never unprovable.
        if self.proof.is_some() {
            let provable = new_lits.len() >= 2
                && drop
                    .iter()
                    .all(|&l| self.proof_unit_id_get_or_zero(l.negate().to_dimacs()) != 0);
            if !provable {
                return false;
            }
            self.proof_strengthen_clause(cid, &new_lits);
        }
        match new_lits.len() {
            0 => {
                self.trivially_unsat = true;
                self.elim_retire_clause_lits(ctx, cid, &lits);
                return false;
            }
            1 => {
                // Strengthened to a unit: apply it eagerly.
                let unit = new_lits[0];
                self.elim_retire_clause_lits(ctx, cid, &lits);
                self.elim_assign_unit(ctx, unit);
                return false;
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
            if let Some(pos) = ctx.occs.position(code, cid) {
                ctx.occs.swap_remove(code, pos);
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
        true
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
                // The elimination derived a unit contradicting an earlier
                // one. Under LRAT both unit clauses are in the proof stream
                // with ids (every elim unit emission records its id), so the
                // empty clause is RUP over exactly those two units — the
                // first propagates its literal, the second conflicts. Seed
                // the chain for `drat_emit_empty(None)`; a missing id leaves
                // it empty (verdict still correct, proof degraded).
                if self.lrat && self.lrat_chain.is_empty() {
                    let a = self.proof_unit_id_get_or_zero(lit.negate().to_dimacs());
                    let b = self.proof_unit_id_get_or_zero(lit.to_dimacs());
                    if a != 0 && b != 0 {
                        self.lrat_chain.push(a);
                        self.lrat_chain.push(b);
                    }
                }
                self.trivially_unsat = true;
                return;
            }
            _ => {}
        }
        ctx.val[lit.code() as usize] = 1;
        ctx.val[lit.negate().code() as usize] = -1;
        ctx.units.push(lit);

        // Retire satisfied clauses.
        let ids: Vec<ClauseId> = ctx.occs.combined(lit.code() as usize);
        for cid in ids {
            self.elim_retire_clause(ctx, cid);
        }
        // Shorten clauses containing the complement.
        let neg = lit.negate();
        let ids: Vec<ClauseId> = ctx.occs.combined(neg.code() as usize);
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
                    let len = ctx.occs.len(lit.code() as usize);
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

        scratch.cands.extend(ctx.occs.iter(best.code() as usize));
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
                        // LRAT: this hyper-unary derivation is RUP with the
                        // same shape as a resolvent — under ¬u, the level-0
                        // units of d's falsified literals make d unit on
                        // `neg`, propagating it, and the subsumer c (which
                        // contains ¬neg and only literals shared with d)
                        // conflicts. Emit BEFORE `elim_assign_unit` retires
                        // d as satisfied (its deletion is a separate,
                        // justification-free line). A missing unit id would
                        // make the chain unverifiable — skip the derivation
                        // instead (weaker, sound).
                        let mut ok_to_assign = true;
                        if self.proof.is_some() {
                            let mut chain: SmallVec<[i64; 8]> = SmallVec::new();
                            let d_lits: Option<SmallVec<[Lit; 8]>> = self
                                .clauses
                                .get(did)
                                .map(|c| c.lits.iter().copied().collect());
                            if let Some(dl) = d_lits {
                                for &l in &dl {
                                    if ctx.lit_val(l) == -1 {
                                        let uid =
                                            self.proof_unit_id_get_or_zero(l.negate().to_dimacs());
                                        if uid == 0 {
                                            ok_to_assign = false;
                                            break;
                                        }
                                        chain.push(uid);
                                    }
                                }
                                if ok_to_assign {
                                    chain.push(self.proof_clause_id(did));
                                    chain.push(self.proof_clause_id(cid));
                                    let pfid = self.proof_next_id();
                                    if let Some(proof) = &mut self.proof {
                                        proof.add_derived_unit_clause(pfid, u.to_dimacs(), &chain);
                                    }
                                    self.proof_set_unit_id(u.to_dimacs(), pfid);
                                }
                            } else {
                                ok_to_assign = false;
                            }
                        }
                        if ok_to_assign {
                            self.elim_assign_unit(ctx, u);
                        }
                        if self.trivially_unsat {
                            break;
                        }
                    } else if ctx.occs.len(neg.code() as usize) <= ELIM_OCC_LIMIT {
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

#[cfg(test)]
mod round_occs_tests {
    use super::*;

    /// Reference differential: every RoundOccs operation must leave the
    /// combined view identical to the plain `Vec<Vec<ClauseId>>` it
    /// replaced, under the eliminator's operation mix (bulk connect with
    /// exact counts, mid-round pushes, flush rewrites, swap_removes,
    /// clears). On failure the op log pinpoints the first divergent op.
    #[test]
    fn round_occs_matches_vec_semantics() {
        let mut rng: u64 = 0x9E3779B97F4A7C15;
        let mut next = || {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            rng
        };
        for round in 0..40u64 {
            let n = 8 + (next() % 24) as usize;
            let counts: Vec<u32> = (0..n).map(|_| (next() % 6) as u32).collect();
            // Generate the connect stream, then apply it to both shapes.
            // Clause ids are unique per list in the eliminator (a clause
            // holds distinct literals, so it connects at most once per
            // literal); duplicates would make `position` ambiguous.
            let mut ids = Vec::new();
            for (code, &c) in counts.iter().enumerate() {
                for _ in 0..c {
                    ids.push((code, ClauseId(next() as u32)));
                }
            }
            let stream = ids;
            let mut ref_occs: Vec<Vec<ClauseId>> = vec![Vec::new(); n];
            let mut occs = RoundOccs::new(n);
            occs.layout(&counts);
            let mut log: Vec<String> = Vec::new();
            let mut fresh = 1_000_000u32 + round as u32 * 10_000;
            for &(code, cid) in &stream {
                ref_occs[code].push(cid);
                occs.connect(code, cid);
                log.push(format!("connect({code}, {cid:?})"));
            }
            for _ in 0..300 {
                let code = (next() as usize) % n;
                match next() % 5 {
                    0 => {
                        // Pushed ids are fresh clause ids (resolvents):
                        // globally unique, like `add_original` returns.
                        fresh += 1;
                        let cid = ClauseId(fresh);
                        ref_occs[code].push(cid);
                        occs.push(code, cid);
                        log.push(format!("push({code}, {cid:?})"));
                    }
                    1 => {
                        if !ref_occs[code].is_empty() {
                            let pos = (next() as usize) % ref_occs[code].len();
                            let cid = ref_occs[code][pos];
                            assert_eq!(
                                occs.position(code, cid),
                                Some(pos),
                                "position mismatch round {round} after ops: {log:?}"
                            );
                            ref_occs[code].swap_remove(pos);
                            occs.swap_remove(code, pos);
                            log.push(format!("swap_remove({code}, {pos})"));
                        }
                    }
                    2 => {
                        // Flush rewrite: keep a prefix, stably sorted.
                        let keep = (next() as usize) % (ref_occs[code].len() + 1);
                        let mut kept: Vec<ClauseId> = ref_occs[code][..keep].to_vec();
                        kept.sort_by_key(|&c| c.0);
                        ref_occs[code] = kept.clone();
                        occs.rewrite(code, &kept);
                        log.push(format!("rewrite({code}, keep={keep})"));
                    }
                    3 => {
                        ref_occs[code].clear();
                        occs.clear(code);
                        log.push(format!("clear({code})"));
                    }
                    _ => {}
                }
                assert_eq!(
                    occs.len(code),
                    ref_occs[code].len(),
                    "len mismatch round {round} code {code} after ops: {log:?}"
                );
                assert_eq!(
                    occs.combined(code),
                    ref_occs[code],
                    "combined mismatch round {round} code {code} after ops: {log:?}"
                );
            }
        }
    }
}
