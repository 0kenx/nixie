//! Clause learning, LBD computation, database reduction, inprocessing, and vivification

use super::*;
use smallvec::SmallVec;

/// How many materialized theory-reason clauses mark a "propagation storm"
/// workload, after which further theory propagations keep lazy explanations
/// (see [`Solver::theory_lazy_reasons_enabled`]).  Calibrated against the QF_UF
/// quasigroup family: medium inputs fire up to ~0.4M equality-atom propagations
/// and run fastest with every reason materialized (BCP re-derives them for
/// free after backtracks); the storm outlier fires 7.68M and loses ~1.5× to
/// the clause-database bloat.  1M sits an order of magnitude above the medium
/// files' entire workload and ~13% into the storm, so it flips only the inputs
/// that are actually drowning.
pub(super) const THEORY_LAZY_SWITCH_AFTER: u64 = 1_000_000;

/// Whether the per-inprocess-round cost/yield trace is on
/// (env var `NIXIE_INPROC_TRACE`).
///
/// Same `OnceLock` pattern as [`super::decide::trace_decisions_enabled`]: one
/// cached bool load when off, no search-path effect either way.
#[cfg(feature = "std")]
pub(super) fn inproc_round_trace_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("NIXIE_INPROC_TRACE")
            .is_ok_and(|v| !v.is_empty() && v != "0" && !v.eq_ignore_ascii_case("false"))
    })
}

#[cfg(not(feature = "std"))]
pub(super) fn inproc_round_trace_enabled() -> bool {
    false
}

/// Whether the effort-relative inprocessing-round schedule is on (env
/// `NIXIE_INPROC_SCHED=1`; study `2026-09-07-inproc-effort-schedule.md`).
/// cadical `SET_EFFORT_LIMIT` shape: each mid-search round's pass budgets are
/// a fixed per-mille of the search work since the last round, and the round
/// interval grows `interval × log10(rounds + 9)` (cadical `inprobe`).
/// Default off: the legacy flat interval and absolute budgets run, keeping
/// the binary trajectory-identical to the pre-change build.
#[cfg(feature = "std")]
pub(super) fn inproc_sched_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("NIXIE_INPROC_SCHED")
            .is_ok_and(|v| !v.is_empty() && v != "0" && !v.eq_ignore_ascii_case("false"))
    })
}

#[cfg(not(feature = "std"))]
pub(super) fn inproc_sched_enabled() -> bool {
    false
}

/// The matched-null arm of the effort schedule (env
/// `NIXIE_INPROC_SCHED_NULL=1`; implies the schedule).  Budgets use the
/// search-work window observed **two rounds earlier** instead of the current
/// one: identical budget magnitudes and timing, the correlation between
/// "work since the last round" and "this round's budget" severed (the
/// lag-2 scramble; windows on the corpus vary 2–3× across adjacent rounds,
/// so the null genuinely perturbs).  Rounds without two predecessors use
/// their true window (nothing to lag from).
#[cfg(feature = "std")]
pub(super) fn inproc_sched_null() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("NIXIE_INPROC_SCHED_NULL")
            .is_ok_and(|v| !v.is_empty() && v != "0" && !v.eq_ignore_ascii_case("false"))
    })
}

#[cfg(not(feature = "std"))]
pub(super) fn inproc_sched_null() -> bool {
    false
}

/// `NIXIE_INPROC_VIVON=1`: disable the cadical `vivifythresh` skip in the
/// effort schedule (study arm; see `inproc_round_budgets`).
#[cfg(feature = "std")]
pub(super) fn vivify_thresh_disabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("NIXIE_INPROC_VIVON")
            .is_ok_and(|v| !v.is_empty() && v != "0" && !v.eq_ignore_ascii_case("false"))
    })
}

#[cfg(not(feature = "std"))]
pub(super) fn vivify_thresh_disabled() -> bool {
    false
}

/// One round's effort-relative budgets (cadical per-mille efforts; see
/// `Solver::inproc_budgets`).
#[derive(Clone, Copy, Debug)]
pub(crate) struct InprocBudgets {
    /// Search-propagation window this round scales against.  `0` marks a
    /// non-scheduled invocation (pre-search one-shot): passes fall back to
    /// their legacy absolute budgets.
    pub window: u64,
    /// Vivify propagation budget (cadical `vivifyeffort` = 50‰ of window;
    /// skipped entirely below `vivifythresh × clauses` — cadical skips the
    /// pass, it does not run it at a floor).
    pub vivify_props: u64,
    /// Whether the vivify pass may run at all this round.
    pub vivify_allowed: bool,
    /// Subsumption-check budget (cadical `subsumeeffort` = 1000‰ of
    /// cumulative *search* propagation, clamped
    /// `[subsumemineff, subsumemaxeff]`).
    pub subsume_checks: u64,
    /// Transitive-reduction step budget (cadical `transredeffort` = 100‰
    /// of the window; our steps are a close analogue of its tick budget).
    pub transred_steps: u64,
    /// Mid-search BVA pair-index build cap (entries) — a work bound in the
    /// scan's own unit (kissat budgets `factor` at 50‰ of window ticks;
    /// entries ≈ clauses × pairs are the scan's dominant cost).
    pub bva_entries: u64,
    /// Mid-search BVA introduction cap for this round.
    pub bva_intros: u64,
}

impl InprocBudgets {
    /// Legacy (non-scheduled) budgets: passes use their own absolute caps.
    pub(super) fn legacy() -> Self {
        Self {
            window: 0,
            vivify_props: 0,
            vivify_allowed: true,
            subsume_checks: 0,
            transred_steps: 0,
            bva_entries: 0,
            bva_intros: 0,
        }
    }
}

impl Solver {
    /// The mid-search inprocessing interval currently in force.  Under the
    /// effort schedule (`NIXIE_INPROC_SCHED`) this grows with completed
    /// rounds — cadical `inprobe`: `delta = interval × log10(rounds + 9)` —
    /// so late rounds fire increasingly rarely on long-running instances.
    /// Without the flag this is exactly `config.inprocessing_interval`
    /// (legacy flat schedule, bit-identical trajectories).
    pub(super) fn inproc_interval_now(&self) -> u64 {
        if !inproc_sched_enabled() {
            return self.config.inprocessing_interval;
        }
        let growth = ((self.inproc_rounds_done + 9) as f64).log10().max(1.0);
        ((self.config.inprocessing_interval as f64) * growth).ceil() as u64
    }

    /// Compute the effort-relative budgets for the mid-search round about
    /// to run, from `window` (search propagation since the last round) and
    /// `null_window` (the lag-2 null's substitute; equal to `window` in the
    /// treatment arm).  cadical reference values: `vivifyeffort` 50,
    /// `vivifythresh` 20, `subsumeeffort` 1000 with min/max efforts 1e6/1e9,
    /// `transredeffort` 100.
    pub(super) fn inproc_round_budgets(&self, window: u64, null_window: u64) -> InprocBudgets {
        let w = if inproc_sched_null() {
            null_window
        } else {
            window
        };
        // cadical `vivifythresh`: skip vivify when the effort allowance is
        // below `thresh × live clauses` (20‰×clauses… exactly: thresh(20) ×
        // clauses.size(), against the tick-scaled delta; ticks ≈ props at
        // this granularity — deviation noted in the study).
        let live = (self.clauses.num_original() + self.clauses.num_learned()) as u64;
        let vivify_sized = w.saturating_mul(VIVIFY_EFFORT_PERMILLE) / 1000;
        // `NIXIE_INPROC_VIVON=1` disables the cadical skip (τ=0): vivify
        // still runs under its effort budget, just never skipped by the
        // threshold — the arm for instances whose measured win tracks
        // vivify's semantic effect rather than its volume.
        let vivify_allowed = vivify_sized
            > if vivify_thresh_disabled() {
                0
            } else {
                VIVIFY_THRESH.saturating_mul(live)
            };
        // cadical subsume: cumulative-search-props × 1000‰, clamped.
        let cum_search = self
            .stats
            .propagations
            .saturating_sub(self.inproc_round_props_total);
        let subsume_checks = cum_search.clamp(SUBSUME_MIN_CHECKS, SUBSUME_MAX_CHECKS);
        InprocBudgets {
            window: w,
            vivify_props: vivify_sized,
            vivify_allowed,
            subsume_checks,
            transred_steps: (w.saturating_mul(TRANSRED_EFFORT_PERMILLE) / 1000)
                .max(TRANSRED_MIN_STEPS),
            bva_entries: w.clamp(200_000, MAX_PAIR_INDEX_ENTRIES_BUDGET),
            bva_intros: (w / 1000).clamp(50, 10_000),
        }
    }
}

/// cadical effort constants for the inprocessing schedule (see
/// `inproc_round_budgets`).
const VIVIFY_EFFORT_PERMILLE: u64 = 50;
const VIVIFY_THRESH: u64 = 20;
const SUBSUME_MIN_CHECKS: u64 = 1_000_000;
const SUBSUME_MAX_CHECKS: u64 = 1_000_000_000;
const TRANSRED_EFFORT_PERMILLE: u64 = 100;
const TRANSRED_MIN_STEPS: u64 = 10_000;
const MAX_PAIR_INDEX_ENTRIES_BUDGET: u64 = 8_000_000;

impl Solver {
    /// Install the consequence of a freshly learned clause on the trail.
    ///
    /// This is the single place where a learned clause's asserting literal gets
    /// assigned, and it is where chronological backtracking's central invariant
    /// lives: **a propagated literal's decision level is the maximum level over
    /// the other literals of its reason clause, not the level the search happens
    /// to sit at.**
    ///
    /// Without chronological backtracking those two coincide, because a backjump
    /// always lands exactly on the assertion level. With it the solver
    /// deliberately stops above the assertion level and keeps the intervening
    /// decisions, so recording the current level instead would claim the literal
    /// depends on decisions it does not depend on. That is not merely imprecise:
    /// a **unit** learned clause is a consequence of the formula alone and must
    /// be pinned at level 0, and recording it at the post-backtrack level both
    /// loses it on the next rollback and plants a second reason-less literal
    /// inside a decision level, which breaks the termination invariant of the
    /// 1-UIP walk in [`Solver::analyze`] and lets it emit clauses that are
    /// stronger than what resolution derives – a direct route to a false `unsat`.
    ///
    /// The clause is asserted only when it really is unit under the
    /// post-backtrack assignment. A degenerate analysis result (two literals at
    /// the top level, which the theory-propagation path can still produce) is
    /// therefore added to the database but not propagated, rather than
    /// overwriting a live trail entry.
    ///
    /// Reference: Z3's `sat_solver.cpp` (`assign_core` / `propagate_clause`
    /// compute the same `assign_level`).
    pub(super) fn assert_learned_clause(&mut self, lits: &[Lit], clause_id: ClauseId) {
        let Some(&asserting) = lits.first() else {
            return;
        };

        if self.trail.is_assigned(asserting.var()) {
            // Already satisfied is fine – nothing to install. Already *falsified*
            // is not: every caller backtracks to a level strictly below the
            // asserting literal's own before getting here (`analyze` and
            // `analyze_theory_conflict` both assert that invariant, and
            // `analyze_theory_asserting_lemma` picks an unassigned literal for
            // index 0), so the literal must be free. If it ever were false the
            // silent return would drop a refutation on the floor: a unit lemma is
            // stored without watches, and a longer clause gets both of its watches
            // pinned on literals that are already false, whose watch events have
            // been and gone. Either way nothing re-examines the clause and the
            // search can go on to report `Sat` over a trail that falsifies it.
            debug_assert!(
                !self.trail.lit_value(asserting).is_false(),
                "learned clause {lits:?} is already falsified at its asserting literal \
                 (level {}, search at level {}); returning silently would drop the refutation",
                self.trail.level(asserting.var()),
                self.trail.decision_level()
            );
            return;
        }

        if lits.len() == 1 {
            self.trail.assign_unit_fact(asserting);
            return;
        }

        let mut level = 0;
        for &lit in &lits[1..] {
            if !self.trail.lit_value(lit).is_false() {
                // Not actually unit – do not fabricate a propagation.
                return;
            }
            level = level.max(self.trail.level(lit.var()));
        }

        self.trail
            .assign_propagation_at(asserting, clause_id, level);
        // LRAT: when every falsified sibling sits at level 0 the asserting
        // literal is installed as a **level-0 propagation** outside
        // `propagate()` — the two flush sites there never see it, so without
        // this flush the literal lands on the trail with no unit-table
        // entry. The "every level-0 literal is a unit with an id" invariant
        // that `analyze`'s RUP chains rely on breaks, and the first conflict
        // chain through such a literal emits a 0 hint — an unverifiable
        // proof (repro: 6s167-opt with LRAT attached; found 2026-09-02).
        // The flush builds exactly the right chain: the level-0 units of
        // the clause's other literals + this clause's id.
        if level == 0 {
            self.flush_level0_unit(asserting, clause_id);
        }
    }

    /// Compute LBD (Literal Block Distance) of a clause
    /// LBD is the number of distinct decision levels in the clause
    pub(super) fn compute_lbd(&mut self, lits: &[Lit]) -> u32 {
        self.lbd_mark = self.lbd_mark.wrapping_add(1);
        if self.lbd_mark == 0 {
            // Wrapped onto the virgin-slot sentinel: reset once and restart
            // the generation sequence (same guard as
            // `conflict::compute_lbd_stamped`, which shares this counter).
            self.level_marks.fill(0);
            self.lbd_mark = 1;
        }
        let mark = self.lbd_mark;

        let mut count = 0u32;
        for &lit in lits {
            let level = self.trail.level(lit.var()) as usize;
            if level < self.level_marks.len() && self.level_marks[level] != mark {
                self.level_marks[level] = mark;
                count += 1;
            }
        }

        count
    }

    /// Learn a clause and set up watches
    /// Includes on-the-fly subsumption check
    /// Tracks allocation via memory optimizer for size-class pool accounting
    /// Feed one learned clause's LBD into the restart machinery: the cadical
    /// per-mode glue EMAs (which drive the focused-mode restart condition) and
    /// the reluctant-doubling tick (which drives stable-mode restarts).
    ///
    /// Called from **every** clause-learning path – `learn_clause` here and the
    /// plain `solve()` loop's inline learner in `solver/mod.rs` – so both the
    /// plain SAT search and the CDCL(T) search (`solve_with_theory`) restart on
    /// the same signal.  Previously only `solve()` updated these, so
    /// `solve_with_theory`'s Glucose restarts fired unconditionally every
    /// `restart_interval` conflicts (the EMA gate read eternally-fresh zeros):
    /// on the QF_UF quasigroup benchmarks that wiped the trail every 100
    /// conflicts and the search needed ~45× more conflicts than Z3.
    pub(super) fn note_learned_lbd(&mut self, lbd: u32) {
        // cadical feeds the restart EMAs with the *analysis-walk* glue
        // (`levels.size() - 1` over the whole 1-UIP resolution walk), not the
        // stored clause's LBD – the walk statistic is larger and far noisier,
        // which is what makes the focused Glucose condition
        // (`fast >= margin × slow`) cross early and often instead of
        // hovering below 1.0 on smooth fat-clause streams.  The clause LBD
        // (`lbd`) continues to feed everything clause-shaped below (tiering
        // happens in `learn_clause` via `compute_lbd`; the recent/global sums
        // feed the LocalLbd strategy and stats).
        //
        // Matched null (`NIXIE_GLUE_NULL=1`): feed the *previous* conflict's
        // walk glue instead – same work, same distribution, same timing, no
        // current-conflict information – so a measured win can be attributed
        // to the walk glue's semantics rather than to the noise level or the
        // trajectory reshuffling the change induces (docs/BENCHMARKING.md).
        let ema_glue = if crate::glue_null_enabled() {
            self.analysis_walk_glue_prev
        } else if crate::glue_legacy_enabled() {
            // A/B switch for the study: the pre-port EMA input (the stored
            // clause's LBD) – see docs/studies.
            lbd
        } else {
            self.analysis_walk_glue
        };
        self.analysis_walk_glue_prev = self.analysis_walk_glue;
        let g = f64::from(ema_glue);
        self.glue_current.fast.update(g);
        self.glue_current.slow.update(g);

        self.reluctant.tick();
        self.recent_lbd_sum += u64::from(lbd);
        self.recent_lbd_count += 1;
        self.global_lbd_sum += u64::from(lbd);
        self.global_lbd_count += 1;
        if self.recent_lbd_count >= 5000 {
            self.recent_lbd_sum /= 2;
            self.recent_lbd_count /= 2;
        }
    }

    pub(super) fn learn_clause(&mut self, mut learnt_clause: SmallVec<[Lit; 32]>) {
        // Track allocation in memory optimizer for pool accounting
        let _pool_buf = self.memory_optimizer.allocate(learnt_clause.len());

        // Record the learned clause in the proof (no-op unless enabled). It is
        // RUP-derivable from the current database by 1-UIP construction; the
        // returned id is bound to the stored clause in each branch below.
        let proof_id = self.proof_learn_clause(&learnt_clause);

        if learnt_clause.len() == 1 {
            // Store unit learned clause in database for persistence across backtracks
            let clause_id = self.clauses.add_learned(learnt_clause.iter().copied());
            self.proof_set_clause_id(clause_id, proof_id);
            self.stats.learned_clauses += 1;
            self.stats.unit_clauses += 1;
            self.learned_clause_ids.push(clause_id);

            // Record the learned clause at the current assertion scope so a
            // SAT-level `pop` retracts it together with the scope's original
            // clauses.  A learned clause is entailed by the clause set *at
            // learn time*; if the pop removes premises (user `(pop)`, the BV
            // solver's probe scopes), a surviving clause may be unentailed and
            // poison every later search – the push/learn/pop/check leak.  The
            // old inlined `solve` loop did this recording; `learn_clause` (the
            // unified path) silently dropped it, which flipped a SATISFIABLE
            // embedded-BV probe to a false `Unsat` that even the defensive
            // forget-and-retry could not cure (the leaked clauses sat below
            // the retry's checkpoint).  `forget_learned_since` remains the
            // finer-grained cleanup; this is the scope-grained backstop.
            if let Some(current_level_clauses) = self.assertion_clause_ids.last_mut() {
                current_level_clauses.push(clause_id);
            }

            self.assert_learned_clause(&learnt_clause, clause_id);
        } else if learnt_clause.len() == 2 {
            // Binary learned clause - add to binary implication graph
            let lbd = self.compute_lbd(&learnt_clause);
            self.note_learned_lbd(lbd);
            let clause_id = self.clauses.add_learned(learnt_clause.iter().copied());
            self.proof_set_clause_id(clause_id, proof_id);
            self.stats.learned_clauses += 1;
            self.stats.binary_clauses += 1;
            self.stats.total_lbd += lbd as u64;

            self.clauses.set_lbd(clause_id, lbd);
            self.clauses.assign_tier_from_lbd(clause_id);
            self.debug_check_learned_clause_lbd(clause_id);

            self.learned_clause_ids.push(clause_id);
            if let Some(current_level_clauses) = self.assertion_clause_ids.last_mut() {
                current_level_clauses.push(clause_id);
            }

            let lit0 = learnt_clause[0];
            let lit1 = learnt_clause[1];

            // BIG registration (and the phantom tick count) happens inside
            // `attach_watchers` for binaries – BIG-authoritative BCP, 2026-09.
            self.attach_watchers(clause_id, lit0, lit1);

            self.assert_learned_clause(&learnt_clause, clause_id);
        } else {
            let lbd = self.compute_lbd(&learnt_clause);
            self.note_learned_lbd(lbd);
            self.stats.total_lbd += lbd as u64;
            let clause_id = self.clauses.add_learned(learnt_clause.iter().copied());
            self.proof_set_clause_id(clause_id, proof_id);
            self.stats.learned_clauses += 1;

            self.clauses.set_lbd(clause_id, lbd);
            self.clauses.assign_tier_from_lbd(clause_id);
            self.debug_check_learned_clause_lbd(clause_id);

            self.learned_clause_ids.push(clause_id);
            if let Some(current_level_clauses) = self.assertion_clause_ids.last_mut() {
                current_level_clauses.push(clause_id);
            }

            // Second watch: the literal that stays "watchable" longest, i.e. the
            // false one at the highest decision level (`watch_rank`), not blindly
            // `learnt_clause[1]`.
            //
            // Soundness, not tuning.  `learnt_clause[0]` is the asserting literal
            // and is fine as the first watch, but index 1 is only the correct
            // second watch when `analyze` happens to leave the highest-level
            // literal there.  `analyze_theory_conflict` builds its clause from a
            // theory explanation whose literals arrive in the theory's order, so
            // index 1 can be a literal that backtracking leaves false *below* the
            // level we return to.  Both watches then sit on literals that are
            // already false and never change again, the watch events never fire,
            // and the clause stops being enforced: `propagate` reports no conflict
            // while the clause is falsified.
            //
            // This restores for learned clauses the same invariant `add_clause`
            // already maintains for original ones (see `watch_rank`).  It is a
            // latent-hole fix found while chasing the QF_UF quasigroup wrong
            // answers, not the cause of those – they were traced to
            // `check_hyper_binary_resolution`.
            let lit0 = learnt_clause[0];
            let mut best = 1;
            for i in 2..learnt_clause.len() {
                if self.watch_rank(learnt_clause[i]) > self.watch_rank(learnt_clause[best]) {
                    best = i;
                }
            }
            // Soundness: `propagate`'s watcher scan requires the two watched
            // literals to live at positions [0] and [1] of the stored clause.
            // When it fires on a falsified watch it swaps that literal to
            // position 1, reads the other watch from `lits[0]`, and searches
            // for a replacement only over the tail `j >= 2` — it *never*
            // examines `lits[1]`. Selecting `best` without moving it to
            // position 1 therefore leaves the second watch out in the tail:
            // the day it falsifies, the scan reads some unrelated `lits[0]`
            // as the "other watch", skips the still-unassigned `lits[1]`, and
            // assigns `lits[0]` from a clause that is not unit. That
            // fabricates a trail fact with a reason clause that is already
            // satisfied, and every conflict resolved through it learns an
            // unentailed clause — observed as false UNSAT on SATISFIABLE
            // `si2-b03m-m800-03` / `circuit_48in64out…dist128_seed1`
            // (CaDiCaL models verified). Swap the chosen literal into place
            // in the stored clause *and* the local vector (they must remain
            // identical: `assert_learned_clause` reads `learnt_clause` below),
            // exactly like `add_clause` and `replace_clause_lits` do.
            if best != 1 {
                learnt_clause.swap(1, best);
                self.clauses.swap_lits(clause_id, 1, best);
            }
            let lit1 = learnt_clause[1];
            self.attach_watchers(clause_id, lit0, lit1);

            self.assert_learned_clause(&learnt_clause, clause_id);

            // NOTE: no per-learned-clause database subsumption scan here
            // (cadical parity). The previous `check_subsumption` call walked
            // the append-only `learned_clause_ids` table for *every* short
            // low-glue learned clause – an O(learned) scan whose cost grows
            // quadratically over the search (measured on `crn_11_99_u`:
            // ~30% of all instructions were this scan's random-access id
            // probes). CaDiCaL never scans the database per learned clause:
            // bulk subsumption is the periodic `subsume` round (our
            // `subsume_round`, run by the inprocessing schedule), and its
            // on-the-fly strengthening only ever rewrites the conflict's own
            // driving clause. Subsumed learned clauses that linger until the
            // next reduction are cadical's behavior too.
        }
    }

    /// Check if the given clause subsumes any existing clauses
    /// A clause C subsumes C' if all literals of C are in C'
    #[expect(dead_code)]
    pub(super) fn check_subsumption(&mut self, new_clause_id: ClauseId) {
        let new_clause: Vec<Lit> = match self.clauses.get(new_clause_id) {
            Some(c) => c.lits.to_vec(),
            None => return,
        };

        if new_clause.len() > 10 {
            return; // Don't check subsumption for large clauses (too expensive)
        }

        // Check against learned clauses only
        let mut to_remove = Vec::new();
        for &cid in &self.learned_clause_ids {
            if cid == new_clause_id {
                continue;
            }

            if let Some(clause) = self.clauses.get(cid) {
                // Promoted clauses are OFF LIMITS. `learned_clause_ids` is
                // append-only and never pruned on promotion, so a clause that
                // `subsume_round` promoted to original (cadical
                // `red = !contained || reason->redundant`: it subsumed an
                // *original* and carries that original's deletion obligation
                // permanently) still appears here. Deleting it on the word of
                // a *learned* subsumer drops the obligation — the final model
                // then violates an input clause (false SAT; reproduced by
                // `dominator_hbr_subsuming_original_promotes_resolvent` under
                // `NIXIE_CHRONO_ALWAYS=1`: promoted `(-874,-1072,-1076)`
                // removed here while covering the retired original that the
                // `1082`-elimination resolvent chain depended on).
                if clause.deleted || !clause.learned {
                    continue;
                }
                if clause.lits.len() < new_clause.len() {
                    continue;
                }

                // Check if new_clause subsumes clause
                if new_clause.iter().all(|&lit| clause.lits.contains(&lit)) {
                    to_remove.push(cid);
                }
            }
        }

        // Remove subsumed clauses. `remove_clause` re-points any live
        // trail-reason reference before retiring (an old subsumed clause can
        // be the current reason of an assigned literal; binary reasons
        // escape the `lits[0]` invariant).
        for cid in to_remove {
            self.remove_clause(cid);
            self.stats.deleted_clauses += 1;
        }
    }

    /// Whether theory propagations may keep **lazy** explanations (stored in
    /// [`Solver::theory_prop_reasons`]) instead of materialized reason clauses.
    ///
    /// Adaptive: a materialized reason clause is a *BCP cache* – after any
    /// backtrack the two watches re-derive the propagation nearly for free,
    /// which beats re-explaining it through the theory – so small/medium
    /// workloads want them materialized.  But a propagation-*storm* input
    /// (all-different-heavy QF_UF: 7.68M propagations on
    /// `QG-classification/qg7/gensys_icl_sk004`) buries BCP under millions of
    /// reason clauses – on that file lazy explanations are 1.5× faster – so
    /// once [`THEORY_LAZY_SWITCH_AFTER`] reason clauses have been materialized
    /// the remainder keep lazy explanations.  The switch is one-way within a
    /// solve (a storm does not un-prove itself) and both policies are sound at
    /// any point, so the flip changes only performance.
    ///
    /// Always materializes while a proof tracer is connected: a DRAT/LRAT
    /// proof must be verifiable from the clause database alone.
    pub(super) fn theory_lazy_reasons_enabled(&self) -> bool {
        self.proof.is_none() && self.theory_reason_clauses >= THEORY_LAZY_SWITCH_AFTER
    }

    /// Assign `lit` as a theory propagation whose explanation is kept
    /// **lazy**: the antecedent literals a materialized reason clause would
    /// have carried (`(lit ∨ ¬r0 ∨ …)`) are stored in
    /// the `theory_prop_reasons` table instead of being added to the clause
    /// database.  Conflict analysis and clause minimization resolve *through*
    /// the stored tail exactly as through a reason clause, so the learned
    /// clauses are identical to the materialized design – without the
    /// per-propagation clause that made equality-atom propagation
    /// counterproductive on propagation-dense CDCL(T) inputs (7.68M reason
    /// clauses on `QG-classification/qg7/gensys_icl_sk004`, 2.7× slower than
    /// not propagating at all; z3 keeps theory justifications lazy the same
    /// way – `th_propagate` records the literal, `explain` is only consulted
    /// when conflict resolution actually resolves through it).
    ///
    /// The caller must pass the reason literals in **true** form (each
    /// currently TRUE on the trail, debug-asserted); the false forms ¬r_i are
    /// what resolution iterates, so they are stored pre-negated.  Must not be
    /// called while a proof is connected (see
    /// `theory_lazy_reasons_enabled`).
    pub fn assign_theory_propagation(&mut self, lit: Lit, reason_lits: SmallVec<[Lit; 8]>) {
        debug_assert!(
            self.theory_lazy_reasons_enabled(),
            "theory reasons must be materialized while a proof is connected"
        );
        debug_assert!(
            reason_lits
                .iter()
                .all(|&r| self.trail.lit_value(r).is_true()),
            "every theory reason must be TRUE on the trail at assignment time"
        );
        let tail: SmallVec<[Lit; 8]> = reason_lits.iter().map(|l| l.negate()).collect();
        self.theory_prop_reasons.insert(lit.var(), tail);
        self.trail.assign_theory(lit);
    }

    /// The lazy antecedent tail of a theory-propagated variable, if it has
    /// one.  Returns the literals in **false** form (¬r_i), i.e. exactly the
    /// literals a materialized reason clause would carry after its head.
    ///
    /// Gated on the proof only (not on the adaptive switch): an entry exists
    /// iff its variable was assigned lazily, and resolving through it stays
    /// valid for as long as that assignment is live – the switch state is
    /// irrelevant to the reader.
    pub(super) fn theory_reason_tail(&self, var: Var) -> Option<&SmallVec<[Lit; 8]>> {
        if self.proof.is_some() {
            return None;
        }
        self.theory_prop_reasons.get(&var)
    }

    /// Add a *reasoned* theory explanation clause for a propagation.
    ///
    /// The clause is `(propagated_lit ∨ ¬r0 ∨ … ∨ ¬r_{n-1})`, sound because the
    /// theory guarantees every `r_i` is currently TRUE on the trail, so the
    /// clause is unit under the current assignment and propagates
    /// `propagated_lit`.  The clause is registered as a two-watched learned
    /// clause so that, after any later backtrack, BCP re-derives the
    /// propagation as soon as the reasons are re-established – the
    /// two-watched-literal invariant that keeps the clause enforced.
    ///
    /// `reason_lits` MUST be non-empty.  An empty reason denotes an
    /// *unconditional* theory fact – a level-0 unit, which cannot be
    /// two-watched and which would break 1-UIP conflict analysis if used as a
    /// mid-level propagation reason (the unit resolves to nothing, so the
    /// propagated literal becomes a spurious UIP and the learned clause can
    /// negate a genuinely-forced atom → false UNSAT).  The caller routes
    /// empty-reason propagations through [`Solver::force_theory_unit`].
    ///
    /// Watch literals are picked with [`Solver::watch_rank`] (prefer a
    /// satisfied literal, then an unassigned one, then the latest-falsified)
    /// and swapped into positions 0 and 1 of the stored clause, because the
    /// watcher / propagation loop assumes the watched literals live there.
    /// `propagated_lit` is currently unassigned (the caller only propagates
    /// unassigned variables) and so is the highest-ranked literal – it stays
    /// at index 0; the second watch is the latest-falsified reason, so a watch
    /// always fires on re-falsification.  The previous code watched indices 0
    /// and 1 blindly, which on a clause whose index-1 literal was false below
    /// the eventual backtrack level left both watches cold and the clause
    /// silently unenforced after backtracking.
    pub(super) fn add_theory_reason_clause(
        &mut self,
        reason_lits: &[Lit],
        propagated_lit: Lit,
    ) -> ClauseId {
        debug_assert!(
            !reason_lits.is_empty(),
            "add_theory_reason_clause requires non-empty reasons; empty-reason \
             theory facts must go through force_theory_unit"
        );

        // Build the explanation clause: (propagated_lit ∨ ¬r0 ∨ …).
        let mut clause_lits: SmallVec<[Lit; 8]> = SmallVec::new();
        clause_lits.push(propagated_lit);
        for &lit in reason_lits {
            let neg = lit.negate();
            // Dedup by variable (keep first occurrence so propagated_lit stays
            // at index 0) and skip a degenerate self-negation that would make
            // the clause a tautology (`propagated_lit ∨ ¬propagated_lit`).
            if neg.var() == propagated_lit.var() {
                continue;
            }
            if clause_lits.iter().any(|&l| l.var() == neg.var()) {
                continue;
            }
            clause_lits.push(neg);
        }

        // After dedup at least propagated_lit + one distinct reason remain.
        let n = clause_lits.len();
        debug_assert!(
            n >= 2,
            "theory reason clause collapsed to a unit; route through force_theory_unit"
        );

        // Select the two best watch literals and swap them into positions 0
        // and 1 (the watcher/propagation loop assumes watched literals live
        // there), mirroring `add_clause` / `learn_clause`.
        if n >= 2 {
            let mut best = 0;
            for i in 1..n {
                if self.watch_rank(clause_lits[i]) > self.watch_rank(clause_lits[best]) {
                    best = i;
                }
            }
            clause_lits.swap(0, best);
            let mut second = 1;
            for i in 2..n {
                if self.watch_rank(clause_lits[i]) > self.watch_rank(clause_lits[second]) {
                    second = i;
                }
            }
            clause_lits.swap(1, second);
        }

        let lbd = self.compute_lbd(&clause_lits);
        let clause_id = self.clauses.add_learned(clause_lits.iter().copied());

        // Track as a deletable Local-tier learned clause. Two invariants make
        // demotion sound:
        //
        // * The clause is a *theory lemma* – entailed by the formula – so
        //   deleting it can only lose propagation strength, never soundness;
        //   the CDCL(T) loop re-derives the fact through the theory on demand.
        // * While the propagated literal sits on the trail, the clause is its
        //   `Reason::Propagation`, and `reduce_clause_database` never deletes a
        //   clause that is the current reason of its asserting literal – so
        //   conflict analysis can never dereference a deleted reason.
        //
        // Keeping these clauses in Core (the previous behaviour) materialized
        // *every* equality-atom propagation as a permanent clause: hundreds of
        // thousands of them on all-different-heavy QF_UF inputs, bloating the
        // watch lists BCP scans and erasing the benefit of the propagation
        // itself. Z3 attaches theory explanations as lazy justifications and
        // only learns a clause when conflict resolution actually resolves
        // through it; deletable reasons approximate that laziness while keeping
        // the `Reason::Propagation(ClauseId)` architecture.
        self.learned_clause_ids.push(clause_id);
        if let Some(current_level_clauses) = self.assertion_clause_ids.last_mut() {
            current_level_clauses.push(clause_id);
        }
        self.clauses.set_lbd(clause_id, lbd);

        // Proof: the explanation clause is a valid theory lemma (recorded with an
        // empty RUP chain; bound to the stored clause below).
        let proof_id = self.proof_theory_clause(
            &clause_lits
                .iter()
                .map(|l| l.to_dimacs())
                .collect::<SmallVec<[i32; 8]>>(),
        );
        self.proof_set_clause_id(clause_id, proof_id);

        let lit0 = clause_lits[0];
        let lit1 = clause_lits[1];
        // BIG registration (and the phantom tick count) for a binary reason
        // clause happens inside `attach_watchers` – BIG-authoritative BCP.
        self.attach_watchers(clause_id, lit0, lit1);

        clause_id
    }

    /// Force an *unconditional* theory fact (a propagation the theory reported
    /// with an empty reason clause) as a permanent level-0 unit.
    ///
    /// Must be called at decision level 0 – the caller backtracks to the root
    /// first (see `install_theory_units`).  Stores the unit lemma `[lit]` as a
    /// Core-tier clause (so the DRAT proof records it and it survives clause-db
    /// reduction) and assigns `lit` as a level-0 decision so it persists across
    /// every later backtrack.
    ///
    /// A unit clause cannot be two-watched, and using one as the reason of a
    /// mid-level propagation breaks 1-UIP conflict analysis (the unit resolves
    /// to nothing, so the propagated literal becomes a spurious UIP and the
    /// learned clause can negate a genuinely-forced atom → false UNSAT).
    /// Installing the fact at level 0 keeps it out of 1-UIP resolution (the
    /// `level > 0` filter in `analyze`) while still constraining the search.
    pub(super) fn force_theory_unit(&mut self, lit: Lit) {
        debug_assert_eq!(
            self.trail.decision_level(),
            0,
            "force_theory_unit requires decision level 0 (caller backtracks first)"
        );
        // Store the unit lemma (Core tier, tracked for reduction).
        let clause_id = self.clauses.add_learned(std::iter::once(lit));
        self.learned_clause_ids.push(clause_id);
        // Scope-record like every other learned clause (see `learn_clause`):
        // a level-0 theory fact is entailed by the current scope's atoms;
        // `pop` rolls the trail assignment but must also retract the unit
        // clause, else it survives as an unentailed permanent constraint.
        if let Some(current_level_clauses) = self.assertion_clause_ids.last_mut() {
            current_level_clauses.push(clause_id);
        }
        self.clauses.set_lbd(clause_id, 1);
        self.clauses.promote_to_core(clause_id);

        // Proof: the unit lemma (recorded as a derived unit with empty chain;
        // bound to the stored clause and the unit-id table).
        let proof_id = self.proof_theory_unit(lit.to_dimacs());
        self.proof_set_clause_id(clause_id, proof_id);
        // Assign at level 0 as a decision (no propagation reason): this is the
        // only sound home for a unit, and it survives every backtrack.
        self.trail.assign_decision(lit);
    }

    /// TEMPORARY DIAGNOSTIC: RUP-check `clause` against ORIGINAL
    /// clauses only.  Assumes the negation of every literal and propagates
    /// over originals; a conflict proves entailment.  Runs on a scratch
    /// assignment map; does not touch solver state.
    /// Whether the cadical-reduce study port is active (`NIXIE_CADICAL_REDUCE`
    /// treatment or `NIXIE_CADICAL_REDUCE_NULL` matched null – same trigger
    /// points and deletion counts, scrambled selection). First use sizes the
    /// used-stamp table (dense over clause ids; ids are dense, append-only).
    pub(super) fn cadical_reduce_enabled(&mut self) -> bool {
        if crate::cadical_reduce_enabled()
            || crate::cadical_reduce_null_enabled()
            || crate::reduce_by_used_enabled()
            || crate::reduce_adapt_enabled()
            || crate::reduce_adapt_null_enabled()
            || crate::kissat_reduce_enabled()
        {
            // First use sizes the used-stamp table (dense over clause ids;
            // ids are dense and append-only).
            if self.cadical_used.len() < self.clauses.num_slots() {
                self.cadical_used.resize(self.clauses.num_slots(), 0);
            }
            return true;
        }
        false
    }

    /// kissat `tiers.c compute_tier_limits` for the current mode: the glue
    /// values at which the cumulative used-by-glue histogram reaches 50 %
    /// (`tier1relative` 500‰) and 90 % (`tier2relative` 900‰) of total
    /// clause usage. Fallbacks (2, 6) when nothing has been used yet;
    /// `tier2 = tier1` if usage never reaches the second quantile (kissat's
    /// own edge case). `NIXIE_KISSAT_REDUCE` study arm.
    pub(super) fn kissat_tier_limits(&self) -> (u32, u32) {
        const FALLBACK: (u32, u32) = (2, 6);
        let mode = usize::from(self.stable);
        let hist = &self.kissat_used_hist[mode];
        let total: u64 = hist.iter().sum();
        if total == 0 {
            return FALLBACK;
        }
        let t1_limit = total.saturating_mul(500) / 1000;
        let t2_limit = total.saturating_mul(900) / 1000;
        let mut acc: u64 = 0;
        let mut tier1: Option<u32> = None;
        let mut tier2: Option<u32> = None;
        for (glue, &used) in hist.iter().enumerate() {
            acc += used;
            if tier1.is_none() && acc >= t1_limit {
                tier1 = Some(glue as u32);
            }
            if acc >= t2_limit {
                tier2 = Some(glue as u32);
                break;
            }
        }
        let t1 = tier1.unwrap_or(FALLBACK.0);
        let t2 = tier2.unwrap_or(t1);
        (t1, t2.max(t1))
    }

    /// Whether `cid` is the recorded propagation reason of any of `lits`'s
    /// variables (exact, all-literal scan). The historical O(1) form checked
    /// only `lits[0]` — valid for watch-propagated clauses (propagate assigns
    /// `clause[0]`) but **wrong for BIG-propagated binaries**, whose implied
    /// literal can sit at either position: the binary edge traversal assigns
    /// the edge's target independently of the stored clause order. Deleting a
    /// clause the trail still records as a reason makes conflict analysis
    /// resolve against a deleted clause and produce a spurious empty clause —
    /// a wrong UNSAT (reproducer: `constraints_17_0.4_1.sanitized.cnf` under
    /// `NIXIE_CADICAL_REDUCE_NULL=1`, 2026-09-02; the same escape is named in
    /// the pure-literal cleanup's comment). All deletion guards use this
    /// exact form; see also `remove_clause`/`retire_clause`'s re-pointing.
    pub(super) fn is_live_reason_clause(&self, cid: ClauseId, lits: &[Lit]) -> bool {
        lits.iter().any(|&l| {
            let var = l.var();
            self.trail.is_assigned(var)
                && matches!(self.trail.reason(var), Reason::Propagation(r) if r == cid)
        })
    }

    /// cadical `reduce.cpp` port: schedule + selection policy.
    ///
    /// Schedule (cadical `internal.cpp` + tail of `reduce ()`): the first
    /// reduction fires `reduceinit` (300) conflicts into the search; after
    /// each reduction the next is scheduled at
    /// `conflicts + max(1, reduceint * sqrt(conflicts))` (with `reduceopt=1`,
    /// CaDiCaL's default), scaled by `log10(irredundant / 1e4)` once the
    /// irredundant set exceeds 1e5.
    ///
    /// Selection (cadical `mark_useless_redundant_clauses_as_garbage`): every
    /// live learned clause that is not a current propagation reason gets its
    /// used-stamp decremented; clauses with `glue <= tier1 (2)` and a positive
    /// stamp, and clauses with `glue <= tier2 (6)` and a nearly-maximal stamp,
    /// are protected. The rest are ordered least-useful-first by
    /// `(glue desc, size desc)` (stable, so equal keys keep allocation order =
    /// learn order) and the worst `reducetarget`% (75) are deleted. Analysis
    /// bumps restamp a clause to `max_used` (31) – see the bump site in
    /// `analyze_mark_antecedent`.
    ///
    /// Deliberately not ported here: cadical's satisfied-clause sweep and
    /// falsified-literal removal (`collect.cpp`) – nixie strengthens through
    /// vivification/subsumption instead, and this port isolates the *schedule
    /// + retention policy* effect. Recorded in the study doc.
    pub(super) fn cadical_reduce_if_due(&mut self) {
        const REDUCE_INT: f64 = 25.0; // cadical opts.reduceint
        const REDUCE_TARGET_PCT: usize = 75; // cadical opts.reducetarget
        const TIER1_GLUE: u32 = 2; // cadical opts.reducetier1glue
        const TIER2_GLUE: u32 = 6; // cadical opts.reducetier2glue
        const MAX_USED: u8 = 31; // cadical max_used

        if self.stats.conflicts < self.cadical_reduce_next {
            return;
        }

        // kissat retention shape (`NIXIE_KISSAT_REDUCE`): tier bounds from
        // the per-mode used-by-glue histogram at the 50 %/90 % usage
        // quantiles (kissat `tiers.c compute_tier_limits`, fallbacks 2/6),
        // and a deletion fraction growing from reducelow (50 %) toward
        // reducehigh (90 %) as `high - (high-low)/log10(reductions+9)`
        // (kissat `reduce.c mark_less_useful_clauses_as_garbage`).
        let kissat = crate::kissat_reduce_enabled();
        let (tier1_glue, tier2_glue) = if kissat {
            self.kissat_tier_limits()
        } else {
            (TIER1_GLUE, TIER2_GLUE)
        };
        let target_pct = if kissat {
            let n = self.cadical_reductions + 9; // this round's count + offset
            let high = 900.0_f64;
            let low = 500.0_f64;
            (high - (high - low) / (n as f64).log10()).clamp(0.0, 100.0) as usize
        } else {
            REDUCE_TARGET_PCT
        };

        let null_arm = crate::cadical_reduce_null_enabled();
        let mut candidates: Vec<(
            u32, /*glue*/
            u32, /*size*/
            u32, /*used*/
            ClauseId,
        )> = Vec::new();

        for &cid in &self.learned_clause_ids {
            let Some(v) = self.clauses.get(cid) else {
                continue;
            };
            if v.deleted || !v.learned {
                continue;
            }
            if self.is_live_reason_clause(cid, v.lits) {
                continue;
            }
            // Decrement the used stamp of every surviving candidate first
            // (cadical does this inline in the marking scan). Saturating at 0.
            let slot = cid.index();
            if slot >= self.cadical_used.len() {
                self.cadical_used.resize(slot + 1, 0);
            }
            let used = self.cadical_used[slot];
            if used > 0 {
                self.cadical_used[slot] = used - 1;
            }
            let glue = v.lbd.max(1); // stored LBD; glue-1 units exist as lbd=1
            let size = v.lits.len() as u32;

            // Tier protection (cadical's two keep rules).
            let used_now = if used > 0 { used - 1 } else { 0 };
            if glue <= tier1_glue && used_now > 0 {
                continue;
            }
            if glue <= tier2_glue && used_now >= MAX_USED - 1 {
                continue;
            }
            candidates.push((glue, size, u32::from(used_now), cid));
        }

        let mut to_delete: Vec<ClauseId> = Vec::new();
        if !candidates.is_empty() {
            // Study arm (`NIXIE_REDUCE_BY_USED`, pre-registered in
            // docs/studies/2026-09-02-retention-signal.md): retention
            // *signal* experiment – rank least-used-first instead of
            // worst-glue-first, same schedule, same deletion counts, same
            // tier protection. The 2026-08-22 reduce study measured random
            // deletion beating glue-ranked deletion 2x on stable-300,
            // suggesting the glue signal misleads; usage is the candidate
            // replacement signal. Off by default.
            let by_used = crate::reduce_by_used_enabled();
            // Adaptive arm (`NIXIE_REDUCE_ADAPT` / `NIXIE_REDUCE_ADAPT_NULL`,
            // pre-registered in docs/studies/2026-09-02-adaptive-retention.md):
            // rank by glue only when glue actually ranks usage among the
            // candidates — the best-glue quartile must have a higher mean
            // used-stamp than the worst-glue quartile. The null inverts the
            // choice (same signal, same firing, opposite correlation).
            let adapt = crate::reduce_adapt_enabled();
            let adapt_null = crate::reduce_adapt_null_enabled();
            let rank_by_used = if adapt || adapt_null {
                let n = candidates.len();
                let q = (n / 4).max(1);
                let mut by_glue = candidates.clone();
                by_glue.sort_by_key(|c| c.0);
                let mean_used = |cs: &[(u32, u32, u32, ClauseId)]| {
                    cs.iter().map(|c| f64::from(c.2)).sum::<f64>() / cs.len() as f64
                };
                let glue_informative = mean_used(&by_glue[..q]) > mean_used(&by_glue[n - q..]);
                if adapt {
                    !glue_informative
                } else {
                    glue_informative // inverted matched null
                }
            } else {
                by_used
            };
            if !null_arm && rank_by_used {
                candidates.sort_by(|a, b| a.2.cmp(&b.2).then(b.0.cmp(&a.0)));
                let target = candidates.len() * target_pct / 100;
                for c in candidates.iter().take(target) {
                    to_delete.push(c.3);
                }
            } else if null_arm {
                // MATCHED NULL: delete the same *number* of clauses as the
                // treatment would (same schedule, same target fraction), but
                // chosen pseudo-randomly instead of by glue/size/used – the
                // perturbation without the retention semantics. Partial
                // Fisher-Yates over the tail: uniform over distinct clauses,
                // no replacement.
                let target = candidates.len() * target_pct / 100;
                for i in 0..target {
                    let remaining = candidates.len() - i;
                    let r = (self.rand_u64() as usize) % remaining + i;
                    candidates.swap(i, r);
                    to_delete.push(candidates[i].3);
                }
            } else {
                // Least useful first: larger glue dies earlier, then larger
                // size. Stable sort keeps allocation (= learn) order for ties,
                // matching cadical's stable_sort rationale.
                candidates.sort_by(|a, b| b.0.cmp(&a.0).then(b.1.cmp(&a.1)));
                let target = candidates.len() * target_pct / 100;
                for c in candidates.iter().take(target) {
                    to_delete.push(c.3);
                }
            }
        }

        for cid in to_delete {
            // Detach watchers (watch hygiene identical to the legacy reduce:
            // deleted slots stay readable, so stale watchers are safe, but
            // every visit then pays a cache miss to discover the flag).
            //
            // Binaries additionally need their implication-graph edges
            // purged BEFORE the flag is set: unlike the legacy reducer, this
            // port deletes len == 2 clauses, and the BIG's edge scan never
            // consults the deleted flag — a stale edge keeps PROPAGATING
            // implications of the deleted clause and recording it as fresh
            // trail reasons, which is a wrong-UNSAT (the exact failure
            // `retire_clause`'s purge was added for on Break_unsat_06_07;
            // this port's inline deletion never had it. Reproducer:
            // constraints_17 under `NIXIE_CADICAL_REDUCE_NULL=1`, 2026-09-02).
            let is_binary = self
                .clauses
                .get(cid)
                .is_some_and(|c| !c.deleted && c.lits.len() == 2);
            if is_binary {
                self.purge_binary_edges(cid);
            }
            if let Some(c) = self.clauses.get(cid).filter(|c| !c.deleted)
                && c.lits.len() >= 2
            {
                let w0 = c.lits[0];
                let w1 = c.lits[1];
                self.watches.remove_clause(w0.negate(), cid);
                self.watches.remove_clause(w1.negate(), cid);
            }
            self.drat_delete(cid);
            self.clauses.remove(cid);
            self.stats.deleted_clauses += 1;
        }

        // Arena reclamation, same as the legacy reduce path (cadical runs
        // its garbage collection inside reduce too).
        self.compact_clause_arena_if_due();

        self.debug_check_invariants("after cadical-style reduction");

        // Schedule the next reduction (cadical reduceopt=1 default).
        self.cadical_reductions += 1;
        let mut delta = REDUCE_INT * (self.stats.conflicts.max(1) as f64).sqrt();
        let irredundant = self.clauses.num_original() as f64;
        if irredundant > 1e5 {
            delta *= irredundant.log10() - 4.0;
        }
        let delta = delta.max(1.0) as u64;
        self.cadical_reduce_next = self.stats.conflicts + delta;
    }

    /// Reduce the learned clause database using tier-based deletion strategy
    /// - Core tier (Tier 1): Rarely deleted, only if very inactive
    /// - Mid tier (Tier 2): Delete ~30% based on activity
    /// - Local tier (Tier 3): Delete ~75% based on activity
    pub(super) fn reduce_clause_database(&mut self) {
        use crate::clause::ClauseTier;

        let mut core_candidates: Vec<(ClauseId, f32)> = Vec::new();
        let mut mid_candidates: Vec<(ClauseId, f32)> = Vec::new();
        let mut local_candidates: Vec<(ClauseId, f32)> = Vec::new();

        for &cid in &self.learned_clause_ids {
            if let Some(clause) = self.clauses.get(cid) {
                if clause.deleted {
                    continue;
                }

                // Promoted clauses (learned clauses that subsumed an original
                // – see `subsume_round`) are permanent: they carry the
                // deletion obligation of the original they replaced.
                if !clause.learned {
                    continue;
                }

                // Don't delete binary clauses (very useful)
                if clause.lits.len() <= 2 {
                    continue;
                }

                // A clause that is the current propagation reason of any of
                // its literals must not be deleted: conflict analysis reads
                // reason clauses, and a deleted reason yields garbage
                // (wrong UNSAT). The exact all-literal scan is required
                // even though this path skips binaries: the historical
                // O(1) `lits[0]`-only form rests on the propagate
                // watch-position invariant, which BIG-propagated binaries
                // break (their implied literal can sit at either position)
                // — the identical bug class the cadical-reduce port
                // exhibited live (constraints_17, 2026-09-02), hardened
                // here too so no future edit re-opens it.
                let is_reason = self.is_live_reason_clause(cid, clause.lits);

                if !is_reason {
                    // cadical `reduce.cpp` protects recently-USED glue
                    // clauses from deletion entirely (before any activity
                    // sort): `glue <= tier1limit && used` and
                    // `glue <= tier2limit && used >= max_used-1` are kept.
                    // Our tier-percentage deletion has no such shield (the
                    // 96 %-vs-76 % deletion anomaly, standing-gap study).
                    // `NIXIE_REDUCE_USED_SHIELD=1` (default OFF — the shield
                    // measured corpus-negative here: 23 vs 25 solved on a
                    // 60-file sample; our tier promotions already reward
                    // use, so the shield over-retains under the
                    // tier-percentage policy) shields any clause used
                    // since the last reduction.
                    let protect_used =
                        crate::reduce_used_shield_enabled() && self.clauses.usage_of(cid) > 0;
                    if !protect_used {
                        match clause.tier {
                            ClauseTier::Core => core_candidates.push((cid, clause.activity)),
                            ClauseTier::Mid => mid_candidates.push((cid, clause.activity)),
                            ClauseTier::Local => local_candidates.push((cid, clause.activity)),
                        }
                    }
                }
            }
        }

        // Sort by activity (ascending) - delete low-activity clauses first
        core_candidates.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(core::cmp::Ordering::Equal));
        mid_candidates.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(core::cmp::Ordering::Equal));
        local_candidates
            .sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(core::cmp::Ordering::Equal));

        // Delete different percentages from each tier.  The defaults are
        // 10 % / 30 % / 75 %; the standing-gap study measures retention
        // against cadical's (76 %-deleted overall vs our 96 %) via the
        // `NIXIE_REDUCE_PCT_{CORE,MID,LOCAL}` knobs (percent 0..=100,
        // default = the historical values — unset knobs change nothing).
        // Cached (this fires per reduce round): the three tier percentages,
        // historical defaults 10 / 30 / 75 (see the standing-gap study for
        // the retention experiments behind the knobs).
        static PCT_CORE: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
        static PCT_MID: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
        static PCT_LOCAL: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
        let pct =
            |flag: &'static std::sync::OnceLock<usize>, name: &str, default: usize| -> usize {
                *flag.get_or_init(|| {
                    std::env::var(name)
                        .ok()
                        .and_then(|v| v.parse::<usize>().ok())
                        .filter(|p| *p <= 100)
                        .unwrap_or(default)
                })
            };
        let _ = (&PCT_CORE, &PCT_MID, &PCT_LOCAL);
        let num_core_delete =
            core_candidates.len() * pct(&PCT_CORE, "NIXIE_REDUCE_PCT_CORE", 10) / 100;
        let num_mid_delete = mid_candidates.len() * pct(&PCT_MID, "NIXIE_REDUCE_PCT_MID", 30) / 100;
        let num_local_delete =
            local_candidates.len() * pct(&PCT_LOCAL, "NIXIE_REDUCE_PCT_LOCAL", 75) / 100;

        // Eagerly detach the two watchers of every deleted clause (cadical
        // `detach_clause` in `reduce`). `ClauseDatabase::remove` only flags
        // the clause deleted, so its watchers otherwise stay in the hot
        // lists until BCP happens to falsify their literals – every visit
        // then pays a cache-miss clause load just to discover the flag.
        // Semantics are identical either way (BCP skips deleted clauses), so
        // this is pure watch-list hygiene: the search trajectory is
        // unchanged. The watched literals are at stored positions [0]/[1].
        let detach = |solver: &mut Solver, cid: ClauseId| {
            if let Some(c) = solver.clauses.get(cid).filter(|c| !c.deleted) {
                let w0 = c.lits[0];
                let w1 = c.lits[1];
                solver.watches.remove_clause(w0.negate(), cid);
                solver.watches.remove_clause(w1.negate(), cid);
            }
        };

        for (cid, _) in core_candidates.iter().take(num_core_delete) {
            // Track clause size for memory pool accounting before removal
            if let Some(clause) = self.clauses.get(*cid) {
                let num_lits = clause.lits.len();
                let buf = self.memory_optimizer.allocate(num_lits);
                self.memory_optimizer.free(buf, num_lits);
            }
            self.drat_delete(*cid);
            detach(self, *cid);
            self.clauses.remove(*cid);
            self.stats.deleted_clauses += 1;
        }

        for (cid, _) in mid_candidates.iter().take(num_mid_delete) {
            if let Some(clause) = self.clauses.get(*cid) {
                let num_lits = clause.lits.len();
                let buf = self.memory_optimizer.allocate(num_lits);
                self.memory_optimizer.free(buf, num_lits);
            }
            self.drat_delete(*cid);
            detach(self, *cid);
            self.clauses.remove(*cid);
            self.stats.deleted_clauses += 1;
        }

        for (cid, _) in local_candidates.iter().take(num_local_delete) {
            if let Some(clause) = self.clauses.get(*cid) {
                let num_lits = clause.lits.len();
                let buf = self.memory_optimizer.allocate(num_lits);
                self.memory_optimizer.free(buf, num_lits);
            }
            self.drat_delete(*cid);
            detach(self, *cid);
            self.clauses.remove(*cid);
            self.stats.deleted_clauses += 1;
        }

        // cadical decrements `used` by one per reduce round on every
        // non-deleted candidate (protection thus means "used since roughly
        // the last round"); approximate by halving, which preserves
        // ordering and reaches 0 in O(log rounds).
        if crate::reduce_used_shield_enabled() {
            for &cid in &self.learned_clause_ids {
                self.clauses.decay_usage(cid);
            }
        }

        // Clean up learned_clause_ids (remove deleted clauses)
        self.learned_clause_ids
            .retain(|&cid| self.clauses.get(cid).is_some_and(|c| !c.deleted));

        // Arena reclamation (standing-gap lever 1): reclaim the deleted
        // slots this round (and earlier rounds) created, gated on the
        // garbage ratio so the cost is amortized. Trajectory-neutral by
        // construction: contents, ids and watch-list order all survive.
        self.compact_clause_arena_if_due();

        // Apply memory optimizer recommendations after deletion
        match self.memory_optimizer.recommend_action() {
            MemoryAction::Compact => {
                self.memory_optimizer.compact();
            }
            MemoryAction::ReduceClauseDatabase => {
                // Already reduced; just compact the pool
                self.memory_optimizer.compact();
            }
            MemoryAction::ExpandPools | MemoryAction::None => {
                // No action needed
            }
        }
    }

    /// Clause-arena reclamation (standing-gap lever 1,
    /// `docs/studies/2026-09-01-standing-vs-kissat-gap-decomposition.md`):
    /// relocate live clauses downward in place (kissat-style sweep),
    /// dropping deleted slots and shrink padding, and rewriting the refs
    /// table and every watcher's arena slot in place. Called from both reduce paths every
    /// round (cadical/kissat shape: GC is part of reduce); the gate inside
    /// keeps it amortized O(1) per byte of garbage.
    ///
    /// Trajectory-neutral by construction – clause bytes, ids, watch-list
    /// order and every counter the search reads are preserved; only
    /// physical addresses move (verified by the 54-file identity gate).
    /// `NIXIE_NO_ARENA_COMPACT=1` disables it (A/B and emergency switch).
    pub(super) fn compact_clause_arena_if_due(&mut self) {
        if !crate::arena_compact_enabled() {
            return;
        }
        if self.clauses.compact_arena(&mut self.watches) {
            self.stats.arena_compactions = self.stats.arena_compactions.saturating_add(1);
            self.debug_check_invariants("after clause-arena compaction");
        }
    }

    /// cadical `mark_satisfied_clauses_as_garbage` + `remove_falsified_literals`
    /// (`collect.cpp`), applied after a scheduled reduction when new root-level
    /// facts appeared since the last sweep (cadical's `last.collect.fixed <
    /// stats.all.fixed` gate).
    ///
    /// Why this matters here: without it the database only ever *grows* with
    /// root-fixed state - clauses satisfied at level 0 stay in the watch
    /// lists, and clauses with root-falsified literals carry them forever.
    /// Instrumented-cadical comparison on `j3037` (the conflicts-parity
    /// file): cadical's mean trail *shrinks* over the run (2901 -> 2324
    /// literals) while ours stays flat (3349 -> 3190), and our per-conflict
    /// instruction ratio grows from 1.07x (early window) to 1.36x (full
    /// run) - the late-search bloat this sweep removes.
    ///
    /// Semantics: a clause containing a literal **true at level 0** is
    /// permanently satisfied and retires. A clause containing a literal
    /// **false at level 0** has that literal stripped via
    /// [`Self::remove_literal_and_rewatch`], which re-selects watches and
    /// keeps the proof stream consistent (stripping is exactly
    /// strengthening). Watched positions are safe by the two-watch
    /// invariant: a root-falsified literal can never be a watched literal
    /// (its falsification at level 0 fires the watch and moves it), so the
    /// strip only touches the clause tail; the helper re-selects watches
    /// regardless. Binaries are never stripped (the helper requires >= 3
    /// literals); a root-falsified binary makes its partner a unit, applied
    /// directly at level 0.
    ///
    /// Gated behind `NIXIE_ROOT_SWEEP=1` (**default off**): the mechanism is
    /// cadical-faithful and wins strongly on the database-bloat class
    /// (`j3037` 37 s -> 29 s, `g2-slp` 36 s -> 22 s serial), but unit-heavy
    /// searches regress deeply (Timetable and noL-11-14 go from solving to
    /// 90 s timeouts) - the trade measured net -1 on the 54-file corpus at
    /// the 40 s cap. See the root-sweep section of
    /// `docs/studies/2026-08-30-analyze-quadratics.md`.
    pub(super) fn sweep_root_fixed_clauses(&mut self) {
        // Destructive-simplification gate, mirroring
        // [`Solver::elimination_allowed`]: a retired original is gone from
        // the formula, so it must never outrun an assertion scope that a
        // `pop` could restore (the BV-CEGAR probe scopes caught exactly this
        // as a wrong `sat` before the gate existed), and it must not fight
        // the proof stream or assumption solving. Unlike elimination, the
        // sweep may run above decision level 0: the scan considers only
        // literals *recorded* at level 0, which are prefix-stable.
        // Retire half default ON (`NIXIE_ROOT_SWEEP=0` opts out): the
        // pass-8 wrong-`sat` root cause (embedded-SAT consumers park
        // non-permanent literals at level 0 - see the permanence guard
        // below) is fixed and the full battery is green.
        if !crate::root_sweep_enabled() {
            return;
        }
        // Destructive-simplification gate, mirroring
        // [`Solver::elimination_allowed`]: a retired original is gone from
        // the formula, so it must never outrun an assertion scope that a
        // `pop` could restore, the CDCL(T) refinement loop, the proof
        // stream, or assumption solving. Unlike elimination, the sweep may
        // run above decision level 0: the scan considers only literals
        // *recorded* at level 0, which are prefix-stable.
        if self.assertion_levels.len() > 1
            || self.real_theory_attached
            || !self.destructive_preprocessing_safe()
            || self.proof.is_some()
            || self.lrat
            || self.assumptions_active
        {
            return;
        }
        let fixed_now = self
            .trail
            .level_start(1)
            .min(self.trail.assignments().len());
        if fixed_now <= self.last_sweep_fixed {
            return;
        }
        self.last_sweep_fixed = fixed_now;

        // Deferred effects so the scan itself holds only the immutable arena
        // borrow (same shape as the elimination connect pass).
        let mut to_retire: SmallVec<[ClauseId; 64]> = SmallVec::new();
        // (clause, root-falsified positions)
        let mut to_strip: SmallVec<[(ClauseId, SmallVec<[usize; 4]>); 32]> = SmallVec::new();
        {
            let Solver { clauses, trail, .. } = self;
            // Full-chain derivability for the level-0 prefix (trail order,
            // one pass): a level-0 fact is DERIVED iff its reason is a live
            // original clause and every falsified literal of that clause is
            // itself an earlier DERIVED level-0 fact. This closes the
            // one-level-deep hole (measured on `si2-b03m`: a stripped
            // literal's immediate reason was a live original, but its chain
            // ran through a literal whose reason clause had been retired -
            // `retire_clause`'s reason hygiene re-points those to `Decision`,
            // an unentailed-in-practice fact the strip then harvested into a
            // permanent clause; 18/3008 post-strip clauses unentailed).
            // Propagation appends in causal order, so the reason's other
            // literals always sit earlier on the trail.
            let l0_len = trail.level_start(1).min(trail.assignments().len());
            let mut derived: Vec<bool> = vec![false; l0_len.min(trail.assignments().len()).max(1)];
            derived.truncate(l0_len);
            for ti in 0..l0_len {
                let lit = trail.assignments()[ti];
                let Reason::Propagation(r) = trail.reason(lit.var()) else {
                    continue; // Decision / Theory: not clause-derived
                };
                let Some(rc) = clauses.get(r) else {
                    continue;
                };
                if rc.deleted || rc.learned {
                    continue;
                }
                let chain_ok = rc.lits.iter().all(|&l| {
                    let lv = l.var();
                    if lv == lit.var() {
                        return true;
                    }
                    // Every other literal must be FALSE (that is why the
                    // clause propagated `lit`); its fact must be DERIVED.
                    if !trail.lit_value(l).is_false() {
                        return false;
                    }
                    let ti2 = trail.trail_index(lv) as usize;
                    ti2 < ti && derived[ti2]
                });
                if chain_ok {
                    derived[ti] = true;
                }
            }
            let fact_derived = |var: crate::Var| -> bool {
                let ti = trail.trail_index(var) as usize;
                ti < l0_len && derived[ti]
            };
            for cid in clauses.iter_ids() {
                let Some(c) = clauses.get(cid) else {
                    continue;
                };
                if c.deleted || c.lits.len() < 3 || c.learned {
                    // Binaries are left entirely alone: their retire-side
                    // binary-graph purge reorders edge lists (a trajectory
                    // changer measured to derail Timetable) and their
                    // residual cost is a single blocker check.
                    continue;
                }
                // Reason guard (reduce's `is_reason`, widened to every
                // literal, CLAUSE-level): a clause that is the current
                // propagation reason of ANY of its literals must not be
                // retired or stripped at all - the trail's reason pointer
                // would dangle (retire) or the reason's resolution
                // semantics would change mid-analysis (strip: the literal
                // the clause propagated its literal WITH disappears).
                // The earlier per-literal `continue` shape only skipped the
                // reason literal itself, leaving the clause eligible via
                // its other literals - measured as the strip path's wrong
                // `unsat` on `circuit_48in64out_700g/800g` and `si2-b03m`.
                if c.lits
                    .iter()
                    .any(|&l| matches!(trail.reason(l.var()), Reason::Propagation(r) if r == cid))
                {
                    continue;
                }
                let mut satisfied = false;
                let mut justifier_entailed = false;
                let mut false_pos: SmallVec<[usize; 4]> = SmallVec::new();
                for (i, &l) in c.lits.iter().enumerate() {
                    let var = l.var();
                    if trail.level(var) != 0 {
                        continue; // only ROOT facts are eligible
                    }
                    match trail.lit_value(l) {
                        LBool::True => {
                            satisfied = true;
                            // Permanence guard (the pass-8 root cause): a
                            // level-0 `true` is only a PERMANENT fact when it
                            // is re-derivable from the live original clause
                            // set - i.e. its reason is a live ORIGINAL clause.
                            // Embedded-SAT consumers (the BV layer's
                            // `check_body`) park arbitrary *model decisions*
                            // at level 0 between probes and rewind the trail
                            // with `restore_to_trail_size` on their Unsat
                            // retry; `assert_const` installs constant pins as
                            // bare `Decision`s with no backing clause; and
                            // `forget_learned_since` drops learned units. A
                            // retirement justified by any of those becomes
                            // UN-justified by the rewind (measured: literal
                            // `-670` true-at-level-0 at retirement, false
                            // after; wrong `sat` on
                            // `cegar_mul_low_word_identity_refuted`).
                            if fact_derived(var) {
                                justifier_entailed = true;
                            }
                            break;
                        }
                        LBool::False => false_pos.push(i),
                        LBool::Undef => {}
                    }
                }
                // Strip eligibility uses the same permanence rule per
                // stripped literal: a falsified literal must be
                // re-derivable-false from the permanent clause set, else the
                // strengthening is unsound after a rewind.
                if !false_pos.is_empty() {
                    false_pos.retain(|i| fact_derived(c.lits[*i].var()));
                }
                let satisfied = satisfied && justifier_entailed;
                if satisfied {
                    to_retire.push(cid);
                } else if !false_pos.is_empty() && crate::root_sweep_strip_enabled() {
                    // Stripping lives behind its OWN knob
                    // (NIXIE_ROOT_SWEEP_STRIP=1, default off): it answered a
                    // WRONG `unsat` on `circuit_48in64out_700g/800g` and
                    // `si2-b03m` (SAT files, seed-stable at default,
                    // deterministically unsat with the strip on) - a second,
                    // still-open soundness hole separate from the retire
                    // path's level-0-permanence bug. Its only measured win
                    // (g2-slp 36 s -> 22 s) stays reachable behind the knob.
                    to_strip.push((cid, false_pos));
                }
            }
        }
        for (cid, mut pos) in to_strip {
            // Descending order keeps earlier indices valid across removals;
            // the helper returns early if the clause died or shrank to a
            // binary meanwhile (e.g. an earlier strip retired it).
            pos.sort_unstable();
            for idx in pos.iter().rev().copied() {
                self.remove_literal_and_rewatch(cid, idx);
            }
        }
        for cid in to_retire {
            self.retire_clause(cid);
            self.stats.deleted_clauses += 1;
        }
    }

    /// Handle clause deletion check and restart check
    pub(super) fn handle_clause_deletion_and_restart(&mut self) {
        self.conflicts_since_deletion += 1;
        // Per-conflict inprocessing clock: the old inlined `solve` loop bumped
        // this next to `stats.conflicts`; the unified loop routes every
        // conflict through this handler, so the clock ticks here instead.
        // Without it the periodic-inprocessing schedule below never fires.
        self.conflicts_since_inprocessing += 1;

        if self.cadical_reduce_enabled() {
            // cadical `reducing ()`: schedule-driven, not threshold-driven.
            self.cadical_reduce_if_due();
            self.sweep_root_fixed_clauses();
        } else if self.conflicts_since_deletion >= self.config.clause_deletion_threshold as u64 {
            self.reduce_clause_database();
            self.sweep_root_fixed_clauses();
            self.debug_check_invariants("after clause database reduction");
            self.conflicts_since_deletion = 0;
        }

        // Restart decision, mirroring the plain `solve()` loop's cadical-style
        // logic exactly (see `Solver::solve` in `solver/mod.rs`): focused mode
        // restarts only when the fast glue EMA degrades past the slow one
        // (checked at most every 2 conflicts), stable mode uses the
        // reluctant-doubling trigger, and the legacy strategies keep their
        // interval semantics.  The previous body restarted whenever
        // `conflicts >= restart_threshold` – and with the default Glucose
        // strategy `restart()` extends that threshold by only the bare
        // `restart_interval` (its min-gap), because the *degradation* decision
        // was never evaluated here.  The CDCL(T) search therefore restarted
        // unconditionally every 100 conflicts, which on structured QF_UF inputs
        // (quasigroup existence) prevented any deep proof effort: ~45× more
        // conflicts than Z3 on `gensys_icl_sk004`, with an average learned
        // clause length of 34.
        self.check_stabilize();
        let do_restart = if self.config.enable_stabilize {
            if self.stable {
                self.reluctant.activated()
            } else {
                // Focused Glucose: check every 2 conflicts.
                if self.stats.conflicts < self.lim_restart {
                    false
                } else {
                    self.lim_restart = self.stats.conflicts.saturating_add(2);
                    let slow = self.glue_current.slow.value();
                    let fast = self.glue_current.fast.value();
                    // 10% margin (cadical restartmarginfocused); guard against
                    // the all-zero initial state.
                    slow > 0.0 && fast >= 1.10 * slow
                }
            }
        } else {
            let past_threshold = self.stats.conflicts >= self.restart_threshold;
            let is_glucose = matches!(self.config.restart_strategy, RestartStrategy::Glucose);
            past_threshold && (!is_glucose || self.lbd_ema_fast >= 1.1 * self.lbd_ema_slow)
        };
        if do_restart {
            self.restart();
            // `restart()` lands at decision level 0 only when reuse-trail is
            // off; with reuse-trail on (the default) it backtracks only as far
            // as `reuse_trail()`, so the level-0 consistency invariant does not
            // apply (same reasoning as in `Solver::solve`).
            if !self.config.reuse_trail {
                self.debug_check_restart_consistency();
            }
        } else if self.rephasing() {
            // cadical CDCL loop order: `restarting() → restart()` takes
            // precedence over `rephasing() → rephase()` within one iteration;
            // both are conflict-budgeted and rarely align. The rephase's
            // leading root backtrack supersedes a partial reuse-trail restart,
            // so running both would just redo the rollback.
            self.rephase();
            // Rephase's leading backtrack is a full root backtrack, so the
            // level-0 restart invariant applies regardless of `reuse_trail` —
            // except when the round was a debug no-op (no backtrack ran), in
            // which case the conflict handler's own backtrack level stands.
            if !self.rephase_skipped {
                self.debug_check_restart_consistency();
            }
            self.debug_check_invariants("after rephase");
        }

        // Periodic inprocessing and post-reduction vivification.  This used to
        // live only in `solve`'s (now removed) inlined CDCL loop, so the
        // CDCL(T) path silently ignored `enable_inprocessing` during search –
        // the SMT layer's `balanced` preset has been setting that flag with no
        // effect.  Both search loops now share this handler, so both get the
        // same schedule.  `inprocess` itself refuses to run above decision
        // level 0 or while an LRAT tracer is attached, which keeps these
        // passes exactly as safe mid-search as they were pre-search.
        if self.config.enable_inprocessing
            && self.conflicts_since_inprocessing >= self.inproc_interval_now()
        {
            // 2026-09-04 telemetry (study
            // `2026-09-04-inprocessing-standing-corpus.md` -> gating follow-up):
            // env-gated per-round cost/yield trace.  Purely diagnostic — one
            // `OnceLock` bool load per round, no search-path change (the flag
            // does not feed any decision), so conflict trajectories stay
            // bit-identical with the flag off *and* with it on.
            let trace_pre = inproc_round_trace_enabled().then(|| {
                (
                    self.stats.conflicts,
                    self.stats.propagations,
                    self.clauses.num_original(),
                    self.clauses.num_learned(),
                    self.stats.subsumed_removed
                        + self.stats.self_subsumed
                        + self.stats.shrunken
                        + self.stats.bve_eliminated
                        + self.stats.substitutions
                        + self.stats.deleted_clauses,
                )
            });
            // The scheduled pass backtracks to the root itself (exactly like
            // `try_scheduled_elimination` and cadical's inprocessing entries,
            // which run at `level 0` by construction).  Without this the
            // schedule only fired on conflicts that happened to backjump to
            // level 0 – on instances whose conflicts resolve at non-zero
            // assertion levels the interval silently never triggered.
            if self.trail.decision_level() > 0 {
                self.backtrack_with_phase_saving(0);
            }
            // Effort-schedule study (2026-09-07): budget this round's passes
            // from the search work since the last round, then mark the
            // round.  `inproc_search_props_mark` is only ever written at
            // round end / reset, so the window is pure search-side (and
            // walk-side) propagation.
            let true_window = self
                .stats
                .propagations
                .saturating_sub(self.inproc_search_props_mark);
            let null_window = if self.inproc_window_ring[0] > 0 {
                self.inproc_window_ring[0]
            } else {
                true_window
            };
            self.inproc_budgets = if inproc_sched_enabled() {
                self.inproc_round_budgets(true_window, null_window)
            } else {
                InprocBudgets::legacy()
            };
            let budgets_used = self.inproc_budgets;
            let round_entry_props = self.stats.propagations;
            self.inprocess();
            self.inproc_budgets = InprocBudgets::legacy();
            self.conflicts_since_inprocessing = 0;
            self.inproc_rounds_done += 1;
            self.inproc_round_props_total = self
                .inproc_round_props_total
                .saturating_add(self.stats.propagations.saturating_sub(round_entry_props));
            self.inproc_search_props_mark = self.stats.propagations;
            self.inproc_window_ring = [self.inproc_window_ring[1], true_window];
            if let Some((cf0, props0, orig0, lrnd0, work0)) = trace_pre {
                let props_in_round = self.stats.propagations - props0;
                let work_yield = self.stats.subsumed_removed
                    + self.stats.self_subsumed
                    + self.stats.shrunken
                    + self.stats.bve_eliminated
                    + self.stats.substitutions
                    + self.stats.deleted_clauses
                    - work0;
                eprintln!(
                    "inproc_round: conflicts={cf0} props_in_round={props_in_round} \
                     window={true_window} budget_w={} viv={}/{} sub_ck={} tr={} \
                     orig={}->{} learned={}->{} yield={work_yield} db={} \
                     lbd_ema={:.2}/{:.2} \
                     els={} units={} shr={} sub={} tred={} tfailed={} \
                     pass_props els={} bva={} pure_sub={} vivify={} tred={} bva_n={}",
                    budgets_used.window,
                    budgets_used.vivify_props,
                    budgets_used.vivify_allowed,
                    budgets_used.subsume_checks,
                    budgets_used.transred_steps,
                    orig0,
                    self.clauses.num_original(),
                    lrnd0,
                    self.clauses.num_learned(),
                    self.clauses.num_original() + self.clauses.num_learned(),
                    self.lbd_ema_fast,
                    self.lbd_ema_slow,
                    self.inproc_diag[0],
                    self.inproc_diag[1],
                    self.inproc_diag[2],
                    self.inproc_diag[3],
                    self.inproc_diag[4],
                    self.inproc_diag[5],
                    self.inproc_diag_props[0],
                    self.inproc_diag_props[1],
                    self.inproc_diag_props[2],
                    self.inproc_diag_props[3],
                    self.inproc_diag_props[4],
                    self.stats.bva_introduced,
                );
            }
        }

        // Scheduled probing (cadical `inprobing` → `inprobe ()`): one
        // budgeted round of failed-literal probing over binary-implication
        // roots with hyper-binary derivation, before elimination in the
        // cadical loop order (probing's forced units and hyper-binaries
        // re-arm the eliminator immediately).
        if self.inprobing() {
            let (_, failed, _) = self.probe_round();
            if failed > 0 {
                self.mark_elim_all();
            }
        }

        // Conflict-scheduled one-shot equivalent-literal substitution
        // (cadical parity, see `SolverConfig::presearch_collapse`): the ELS
        // pass that the pre-search collapse used to run unconditionally now
        // fires on the elimination clock instead — sharing `lim_elim` with
        // the eliminator (cadical's `decompose` runs in the same schedule
        // region).
        //
        // The schedule slot (root backtrack + one-shot latch) is
        // UNCONDITIONAL: it has been part of every shipped default
        // trajectory since the conflict-scheduled port (`58df118`), and the
        // presets run with the pass itself off (see `config_presets.rs`),
        // so removing the slot would silently rewrite every default
        // trajectory.  Only the CALL is gated on `enable_equiv_substitution`.
        //
        // This also fixes the silent no-op that slot carried from
        // `58df118` until 2026-09-05: it used to set `did_equiv_subst`
        // BEFORE calling `substitute_equivalent_literals`, whose first line
        // is exactly that one-shot guard — so whenever the pass was enabled
        // the scheduled ELS (and the gate-congruence augmentation it hosts)
        // silently did nothing, and the `0ed8543` "BVE + ELS" default-on
        // measurement had measured BVE alone.  The latch-free `_round`
        // variant (the one `inprocess()` rounds use) is called here now.
        if !self.config.presearch_collapse
            && !self.did_equiv_subst
            && self.stats.conflicts >= self.lim_elim
        {
            if self.trail.decision_level() > 0 {
                self.backtrack_with_phase_saving(0);
            }
            self.did_equiv_subst = true;
            #[cfg(feature = "std")]
            if super::learn::inproc_round_trace_enabled() {
                eprintln!("els_one_shot: firing at conflicts={}", self.stats.conflicts);
            }
            if self.config.enable_equiv_substitution {
                // Same theory-safety gate as the `inprocess()` ELS call: with
                // a real theory attached the round only runs under freeze-set
                // collapse (frozen theory vars stay unfolded inside the SCC
                // fold).
                if self.destructive_preprocessing_safe()
                    && self.substitute_equivalent_literals_round()
                        == super::equiv::SubstOutcome::Unsat
                {
                    self.trivially_unsat = true;
                }
            }
        }

        // Scheduled elimination (cadical `ineliminating` → `elim ()`): runs
        // when the elimination conflict limit has passed *and* something new
        // happened (units fixed at level 0, or original clauses removed or
        // shrunk – which re-marks their variables). Backtracks to the root
        // itself; refused above decision level 0 / under a real theory /
        // with proofs attached / in incremental scopes, exactly like the
        // pre-search phase.
        if self.try_scheduled_elimination() == super::equiv::SubstOutcome::Unsat {
            // An empty resolvent was derived: the formula is UNSAT. There is
            // no falsified clause to seed a proof chain from, so only emit
            // the empty clause for the plain DRAT path (elimination is gated
            // off entirely while LRAT is attached).
            if !self.lrat {
                self.drat_emit_empty(None);
            }
        }
    }

    /// Handle clause deletion and restart, but don't backtrack past assumptions
    pub(super) fn handle_clause_deletion_and_restart_limited(&mut self, min_level: u32) {
        self.conflicts_since_deletion += 1;

        if self.conflicts_since_deletion >= self.config.clause_deletion_threshold as u64 {
            self.reduce_clause_database();
            self.debug_check_invariants("after clause database reduction (assumptions)");
            self.conflicts_since_deletion = 0;
        }

        if self.stats.conflicts >= self.restart_threshold {
            // Limited restart - don't backtrack past assumptions, so unlike
            // `Solver::restart` this does NOT land at decision level 0;
            // `debug_check_restart_consistency` (which asserts exactly that)
            // does not apply here.
            self.backtrack(min_level);
            self.stats.restarts += 1;
            self.luby_index += 1;
            self.restart_threshold =
                self.stats.conflicts + self.config.restart_interval * Self::luby(self.luby_index);
            self.debug_check_invariants("after limited restart (assumptions)");
        }
    }

    /// Save the model
    pub(super) fn save_model(&mut self) {
        self.model.resize(self.num_vars, LBool::Undef);
        for i in 0..self.num_vars {
            self.model[i] = self.trail.value(Var::new(i as u32));
        }

        // Reconstruct pure literals eliminated during inprocessing. Their clauses
        // were deleted on the promise that the literal is fixed to its polarity;
        // the search may have assigned the variable the opposite phase, so force
        // it here. This can only satisfy additional clauses: no remaining clause
        // contains the opposite polarity (that is exactly what "pure" means).
        for &lit in &self.pure_literal_reconstruction {
            let idx = lit.var().index();
            if idx < self.model.len() {
                self.model[idx] = if lit.is_pos() {
                    LBool::True
                } else {
                    LBool::False
                };
            }
        }

        // Reconstruct variables eliminated by equivalent-literal substitution
        // (equiv.rs / congruence.rs): give each the value of its representative
        // literal (flipped when polarities differ). Iterated to a fixpoint so a
        // representative that is itself eliminated (or whose value arrives via
        // BVE reconstruction below) is handled regardless of variable order.
        if !self.equiv_substitution.is_empty() {
            loop {
                let mut changed = false;
                for v in 0..self.num_vars {
                    if self.model[v] != LBool::Undef {
                        continue;
                    }
                    let Some(rep) = self.equiv_substitution.get(v).copied() else {
                        continue;
                    };
                    if rep.var().index() == v {
                        continue; // not eliminated
                    }
                    let Some(rep_val) = self.model.get(rep.var().index()).copied() else {
                        continue;
                    };
                    if rep_val == LBool::Undef {
                        continue; // rep not yet known; retry next iteration
                    }
                    self.model[v] = if rep.is_pos() {
                        rep_val
                    } else {
                        rep_val.negate()
                    };
                    changed = true;
                }
                if !changed {
                    break;
                }
            }
        }

        // Reconstruct variables eliminated by BVE in reverse elimination order.
        // For eliminated `v` with positive clauses `(v ∨ A_i)` (stripped of `v`):
        //   - if EVERY `A_i` already has a satisfied literal, set `v = false`
        //     (the `(v ∨ A_i)` are satisfied without it, and `¬v` satisfies the
        //     `(¬v ∨ B_j)`);
        //   - else SOME `A_k` is all-false, forcing `v = true` to satisfy
        //     `(v ∨ A_k)`. The resolvents `(A_k ∨ B_j)` then guarantee every
        //     `B_j` is true, so the `(¬v ∨ B_j)` are satisfied too.
        // (The earlier version used "any satisfied" → wrong when some but not
        //  all `A_i` are satisfied: it set v=false and violated the all-false
        //  clause.)
        //
        // A variable eliminated by the inprocessing eliminator with an *empty*
        // recorded positive side (all its positive clauses were retired as
        // satisfied before it was eliminated) defaults to `false`: that
        // satisfies every dropped `(¬v ∨ B_j)` and the positive side was
        // already satisfied by unconditional units.
        if !self.bve_order.is_empty() {
            for &v in self.bve_order.iter().rev() {
                let clauses = match self.bve_def.get(v.index()) {
                    Some(c) if !c.is_empty() => c,
                    _ => {
                        if v.index() < self.model.len() {
                            self.model[v.index()] = LBool::False;
                        }
                        continue;
                    }
                };
                let lit_true = |l: Lit| {
                    self.model
                        .get(l.var().index())
                        .copied()
                        .unwrap_or(LBool::Undef)
                        == if l.is_pos() {
                            LBool::True
                        } else {
                            LBool::False
                        }
                };
                let all_satisfied = clauses
                    .iter()
                    .all(|clause| clause.iter().any(|&l| lit_true(l)));
                self.model[v.index()] = if all_satisfied {
                    LBool::False
                } else {
                    LBool::True
                };
            }
        }
    }

    /// Safety net for the purely Boolean entry points: check that the model just
    /// saved actually satisfies the clause database.
    ///
    /// A false `Unsat` merely fails to solve; a false `Sat` hands every
    /// downstream consumer an assignment they will trust. Verifying the finished
    /// model is one linear pass, so in debug builds – which covers every test and
    /// CI run – this converts such corruption into a loud, precisely localised
    /// failure instead of a silently wrong answer. It compiles to nothing in
    /// release, so the shipped hot path is unaffected.
    ///
    /// Deliberately **not** called from `solve_with_theory`; that path has its own
    /// narrower guard, [`Solver::debug_verify_model_input`]. There the database
    /// also holds lemmas injected through `TheoryCallback` (see
    /// [`Solver::add_theory_reason_clause`]) whose validity and lifetime this
    /// crate does not control: the theory retracts its context through
    /// `on_backtrack` without the Boolean core retracting the corresponding
    /// lemma, so a final model may legitimately falsify one. Asserting on those
    /// would make `nixie-sat` fail on behalf of a component it cannot police.
    pub(super) fn debug_verify_model(&self) {
        #[cfg(debug_assertions)]
        if let Some(id) = self.find_model_violation(true) {
            let lits = self.clauses.get(id).map(|c| c.lits.to_vec());
            panic!(
                "solve() reported Sat with a model that violates clause {id:?} ({lits:?}); \
                 the search accepted an assignment that does not satisfy the database"
            );
        }
    }

    /// Safety net for the CDCL(T) entry point [`Solver::solve_with_theory`].
    ///
    /// The full check above cannot be used there, but the reason it cannot –
    /// `TheoryCallback`-injected lemmas whose validity `nixie-sat` does not own –
    /// applies only to *learned* clauses: theory reason clauses and theory lemmas
    /// all enter through `ClauseDb::add_learned`, as do the resolvents that 1-UIP
    /// analysis derives over them. **Original** clauses are a different matter
    /// entirely. They arrived through `add_clause` from the caller, they are the
    /// Boolean abstraction the caller asked to be satisfied, and nothing but
    /// `pop` retracts them. A `Sat` answer that falsifies one is a bug in this
    /// crate no matter what the theory did, so restricting the scan to them gives
    /// a guard that is both meaningful and impossible to trip on the theory's
    /// behalf.
    ///
    /// That is precisely the class the propagation-fixpoint bug produced: an
    /// original ternary clause with all three literals falsified by level-0 facts
    /// while `final_check` answered `Sat`.
    pub(super) fn debug_verify_model_input(&self) {
        #[cfg(debug_assertions)]
        if let Some(id) = self.find_model_violation(false) {
            let lits = self.clauses.get(id).map(|c| c.lits.to_vec());
            panic!(
                "solve_with_theory() reported Sat with a model that violates ORIGINAL clause \
                 {id:?} ({lits:?}); the CDCL(T) search accepted an assignment that does not \
                 satisfy the input formula's Boolean abstraction"
            );
        }
    }

    /// Find a live, *enforced* clause that the saved model does not satisfy.
    ///
    /// The scope is deliberately "everything the two-watched-literal scheme is
    /// responsible for": non-deleted clauses of at least two literals. A model
    /// falsifying one of those means propagation failed to fire on a watch, which
    /// is a soundness bug whether the clause is original or learned. Callers that
    /// cannot vouch for learned clauses pass `include_learned == false`.
    ///
    /// Unit clauses are excluded because the database is not what enforces them.
    /// `add_clause` never stores a unit at all – it assigns the literal at level
    /// 0 – and the copies that learned units leave behind carry no watches; their
    /// force comes solely from that level-0 trail assignment. An incremental
    /// caller that retracts the assignment (`pop`, `restore_to_trail_size`)
    /// without also dropping the record leaves a lemma the formula no longer
    /// entails, which a later model may legitimately falsify.
    ///
    /// Clauses retired by inprocessing are skipped for a similar reason: they are
    /// re-satisfied by model reconstruction rather than by the assignment, and
    /// their literals need not even be in the model's variable range.
    ///
    /// Only consumed from `debug_assertions` safety nets; in release builds the
    /// calls compile away and so does this scan.
    #[cfg_attr(not(debug_assertions), allow(dead_code))]
    pub(super) fn find_model_violation(&self, include_learned: bool) -> Option<ClauseId> {
        self.clauses.iter_ids().find(|&id| {
            self.clauses.get(id).is_some_and(|clause| {
                (include_learned || !clause.learned)
                    && clause.lits.len() >= 2
                    && !clause
                        .lits
                        .iter()
                        .any(|lit| match self.model.get(lit.var().index()) {
                            Some(LBool::True) => lit.is_pos(),
                            Some(LBool::False) => !lit.is_pos(),
                            _ => false,
                        })
            })
        })
    }

    /// Release build: compiles away entirely.
    #[cfg(not(debug_assertions))]
    #[inline]
    pub(super) fn debug_check_invariants(&self, _context: &str) {}

    /// Debug-only structural/soundness net over the whole CDCL data model:
    /// clause well-formedness, trail/assignment consistency, decision-level
    /// bookkeeping, static learned-clause LBD bounds, live reason clauses, and
    /// implication-graph acyclicity. See `crate::invariants` for exactly what
    /// each check covers and why the checks this sweep deliberately does
    /// *not* run are situational instead (only meaningful right after a
    /// specific event, such as a conflict or a restart). Compiles to nothing
    /// in release builds.
    #[cfg(debug_assertions)]
    pub(super) fn debug_check_invariants(&self, context: &str) {
        if let Err(msg) = crate::invariants::check_all_sat_invariants(self) {
            panic!("SAT solver invariant violated ({context}): {msg}");
        }
    }

    /// Release build: compiles away entirely.
    #[cfg(not(debug_assertions))]
    #[inline]
    pub(super) fn debug_check_fixpoint_invariants(&self, _context: &str) {}

    /// Debug-only net for the two invariants that only hold once
    /// `propagate()` has reached a fixpoint (returned `None`): no live clause
    /// has both watched literals false while unsatisfied
    /// (`crate::invariants::check_watched_literals`), and no live clause is a
    /// hanging unit (`crate::invariants::check_unit_propagation_complete`).
    /// Call this only at a fixpoint – mid-scan both are routinely and
    /// harmlessly violated. Compiles to nothing in release builds.
    #[cfg(debug_assertions)]
    pub(super) fn debug_check_fixpoint_invariants(&self, context: &str) {
        if let Err(msg) = crate::invariants::check_watched_literals(self) {
            panic!("SAT solver invariant violated at a propagation fixpoint ({context}): {msg}");
        }
        if let Err(msg) = crate::invariants::check_unit_propagation_complete(self) {
            panic!("SAT solver invariant violated at a propagation fixpoint ({context}): {msg}");
        }
    }

    /// Release build: compiles away entirely.
    #[cfg(not(debug_assertions))]
    #[inline]
    pub(super) fn debug_check_conflict_clause(&self, _conflict: ClauseId) {}

    /// Debug-only net: the clause `propagate()` just reported as a conflict
    /// is fully assigned and fully falsified. Call this right where
    /// `propagate()` returns `Some(conflict)`, before any backtrack changes
    /// the trail. Compiles to nothing in release builds.
    #[cfg(debug_assertions)]
    pub(super) fn debug_check_conflict_clause(&self, conflict: ClauseId) {
        if let Err(msg) = crate::invariants::check_conflict_clause(self, conflict) {
            panic!("SAT solver invariant violated at conflict detection: {msg}");
        }
    }

    /// Release build: compiles away entirely.
    #[cfg(not(debug_assertions))]
    #[inline]
    pub(super) fn debug_check_restart_consistency(&self) {}

    /// Debug-only net: right after a restart, the decision level is 0 and
    /// every trail entry is a level-0 fact. Compiles to nothing in release
    /// builds.
    #[cfg(debug_assertions)]
    pub(super) fn debug_check_restart_consistency(&self) {
        if let Err(msg) = crate::invariants::check_restart_consistency(self) {
            panic!("SAT solver invariant violated after restart: {msg}");
        }
    }

    /// Release build: compiles away entirely.
    #[cfg(not(debug_assertions))]
    #[inline]
    pub(super) fn debug_check_learned_clause_lbd(&self, _clause_id: ClauseId) {}

    /// Debug-only net: a freshly learned clause's stored LBD matches
    /// recomputing it right now. Only sound to call in the instant right
    /// after `clause_id` was learned and its `lbd` field set – see
    /// `crate::invariants::check_learned_clause_lbd`'s doc comment for why
    /// this cannot be a standing, whole-database invariant. Compiles to
    /// nothing in release builds.
    #[cfg(debug_assertions)]
    pub(super) fn debug_check_learned_clause_lbd(&self, clause_id: ClauseId) {
        if let Err(msg) = crate::invariants::check_learned_clause_lbd(self, clause_id) {
            panic!("SAT solver invariant violated for freshly learned clause: {msg}");
        }
    }

    /// Remove the literal at `idx` from a learned clause and rebuild its two
    /// watches so the two-watched-literal invariant is preserved.
    ///
    /// Vivification and inprocessing strengthening shrink a clause in place. If
    /// the removed literal sat at a watched position (index 0 or 1), the stale
    /// watcher would keep pointing at a literal no longer in the clause, breaking
    /// watch firing – a watched literal becoming false would no longer re-examine
    /// the clause, causing missed unit propagations and, if index 0 were removed
    /// repeatedly, a clause left effectively unwatched (a missed conflict). This
    /// detaches the old watches (always keyed on the pre-removal literals at
    /// positions 0 and 1), removes the literal, re-selects the two best watch
    /// literals (mirroring [`Solver::add_clause`]), and re-attaches them.
    pub(super) fn remove_literal_and_rewatch(&mut self, clause_id: ClauseId, idx: usize) {
        self.remove_literal_opts(clause_id, idx, true);
    }

    /// The physical shrink without the default strengthen emission — for
    /// callers that emit their own (resolution-justified) proof event for
    /// the same shrink first (`subsume_round`'s strengthen arm). A double
    /// emission would append two additions and two deletions for one
    /// shrink and desynchronize every later id.
    pub(super) fn remove_literal_and_rewatch_silent(&mut self, clause_id: ClauseId, idx: usize) {
        self.remove_literal_opts(clause_id, idx, false);
    }

    fn remove_literal_opts(&mut self, clause_id: ClauseId, idx: usize, emit_proof: bool) {
        let mut lits: Vec<Lit> = match self.clauses.get(clause_id) {
            Some(c) if !c.deleted && c.lits.len() > 2 && idx < c.lits.len() => c.lits.to_vec(),
            _ => return,
        };

        // Detach the existing watches (keyed on the current positions 0 and 1).
        let old_w0 = lits[0];
        let old_w1 = lits[1];
        self.watches.remove_clause(old_w0.negate(), clause_id);
        self.watches.remove_clause(old_w1.negate(), clause_id);

        // Remove the redundant literal.
        lits.remove(idx);

        // Re-select the two best watch literals: prefer a satisfied literal, then
        // an unassigned one, and finally the latest-falsified. Mirrors
        // `Solver::add_clause` so a watched literal always fires when re-falsified.
        let n = lits.len();
        let mut best = 0;
        for i in 1..n {
            if self.watch_rank(lits[i]) > self.watch_rank(lits[best]) {
                best = i;
            }
        }
        lits.swap(0, best);
        let mut second = 1;
        for i in 2..n {
            if self.watch_rank(lits[i]) > self.watch_rank(lits[second]) {
                second = i;
            }
        }
        lits.swap(1, second);

        let w0 = lits[0];
        let w1 = lits[1];

        // Write the reordered literals back into the clause.
        self.clauses.shrink(clause_id, &lits);
        // Recompute the stored LBD over the shrunken literal set (the old
        // value can exceed the new length – see `replace_clause_lits`).
        if self.clauses.get(clause_id).is_some_and(|c| c.learned) {
            let lbd = self.compute_lbd(&lits);
            self.clauses.set_lbd(clause_id, lbd);
            self.clauses.assign_tier_from_lbd(clause_id);
        }

        // Re-attach watches on the new positions 0 and 1.
        self.attach_watchers(clause_id, w0, w1);

        // Record the in-place strengthening in the proof: add the shorter
        // clause (RUP-derivable – vivification proved it entailed) then delete the
        // original, keeping the proof's clause set consistent with the database.
        if emit_proof && self.proof.is_some() {
            let new_lits: SmallVec<[Lit; 8]> = lits.iter().copied().collect();
            self.proof_strengthen_clause(clause_id, &new_lits);
        }

        // Re-attaching watches is not enough on its own: a watch only ever
        // fires when its literal is *newly* falsified, and the literals that
        // falsify a just-shortened clause are typically already on the trail,
        // propagated long ago.  A clause that had two unassigned literals and
        // loses one becomes unit under the *current* assignment with no
        // future event left to notice it — a "hanging unit" that unit
        // propagation never fires on, losing an implication (which, if it was
        // the one that closed a branch, can change the search enough to
        // matter).  Rewinding is always safe: re-propagating a literal that is
        // still assigned is a no-op. (Ported from upstream v0.3.3.)
        self.trail.reset_propagation_head();
    }

    /// Vivification (asymmetric branching, cadical-style): shorten/strengthen
    /// clauses by assuming their literals false in order and propagating. If a
    /// prefix of literals falsified leads to a conflict, that prefix clause is
    /// implied by the formula, so the clause can be replaced by the (shorter)
    /// prefix. If a later literal of the clause is forced true during the
    /// prefix assignment, the clause (prefix ∨ that-literal) is implied.
    /// Soundness-preserving: the replacement clause is always a consequence of
    /// the formula. Bounded by a deterministic propagation-step budget and a
    /// clause count – *not* wall-clock: a clock-based policy input makes the
    /// solver nondeterministic under load (breaking `run_parity.sh`
    /// reproduction) and burned ~11% of solve time on `clock_gettime` calls.
    pub(super) fn vivify_clauses(&mut self) {
        if self.trail.decision_level() != 0 {
            return;
        }
        const MAX_VIVIFY_PROPS: u64 = 10_000_000;
        const MAX_CLAUSES: usize = 5_000;
        // Effort-scheduled rounds (2026-09-07 study): cadical `SET_EFFORT_LIMIT
        // // (vivify)` — 50‰ of the search window, and the pass is SKIPPED
        // (not floored) when that allowance is below `vivifythresh × live
        // clauses` (cadical vivifythresh = 20).  Legacy rounds keep the
        // absolute 10M budget.
        let scheduled = self.inproc_budgets.window > 0;
        if scheduled && !self.inproc_budgets.vivify_allowed {
            return;
        }
        let prop_budget = if scheduled {
            self.inproc_budgets.vivify_props.max(1)
        } else {
            MAX_VIVIFY_PROPS
        };
        let start_props = self.stats.propagations;
        let done = 0usize;

        // Snapshot candidate ids up front (vivify mutates the clause DB).
        // Learned clauses first (they drive the search), then – when no proof
        // is attached, since an in-place strengthening is not logged as an
        // addition/deletion pair – original clauses (cadical `vivifyirred`):
        // vivifying the irredundant core is what collapses hard combinatorial
        // instances (`noL-*`), where there are no learned clauses yet.
        let mut candidates: SmallVec<[ClauseId; 64]> = self
            .learned_clause_ids
            .iter()
            .copied()
            .take(MAX_CLAUSES)
            .collect();
        if self.proof.is_none() && !self.lrat {
            for cid in self.clauses.iter_ids() {
                if candidates.len() >= 2 * MAX_CLAUSES {
                    break;
                }
                if self
                    .clauses
                    .get(cid)
                    .is_some_and(|c| !c.deleted && !c.learned && c.lits.len() > 2)
                {
                    candidates.push(cid);
                }
            }
        }

        // Snapshot eligible candidates (same budget/eligibility as before),
        // then visit them in TRIE ORDER (POS'25 shared-prefix vivification:
        // lexicographic by literal codes) so consecutive clauses share
        // leading literals and `vivify_clause_shared` keeps those decision
        // levels instead of re-deciding from level 0 per candidate.  The
        // candidate SET and budgets are unchanged.  Measured (6s167-opt,
        // study `2026-08-trie-vivify.md`): identical strengthening (693 vs
        // 709 clauses) at 39% fewer vivify-internal propagations (278k vs
        // 458k); end-to-end neutral over the 94-file corpus — an above-band
        // component win at no system cost, landed per the band rule.
        /// One candidate snapshot: (decision levels prefix, clause, original
        /// literals) — trie order preserves the shared-prefix invariant.
        type Cand = (SmallVec<[u32; 8]>, ClauseId, SmallVec<[Lit; 8]>);
        let mut snapshot: Vec<Cand> = Vec::new();
        for cid in candidates {
            if done >= MAX_CLAUSES
                || self.stats.propagations.saturating_sub(start_props) > prop_budget
            {
                break;
            }
            // Need len > 2 (binary/unit clauses aren't worth vivifying).
            let lits: SmallVec<[Lit; 8]> = match self.clauses.get(cid) {
                Some(c) if !c.deleted && c.lits.len() > 2 => c.lits.iter().copied().collect(),
                _ => continue,
            };
            let key: SmallVec<[u32; 8]> = lits.iter().map(|l| l.code()).collect();
            snapshot.push((key, cid, lits));
        }
        snapshot.sort_by(|a, b| a.0.cmp(&b.0));

        // Shared-prefix state across candidates: the previous candidate's
        // examined-literal prefix and the EXACT decision depth after each
        // prefix index (see `vivify_clause_shared` for why exactness is a
        // soundness requirement).
        let mut prev_lits: SmallVec<[Lit; 8]> = SmallVec::new();
        let mut prev_depths: SmallVec<[u32; 8]> = SmallVec::new();
        let start_subsumed = self.stats.subsumed_removed;
        for (_, cid, lits) in &snapshot {
            if self.stats.propagations.saturating_sub(start_props) > prop_budget {
                break;
            }
            let _ = self.vivify_clause_shared(*cid, lits, &mut prev_lits, &mut prev_depths);
        }
        if crate::vivify_trace_enabled() {
            eprintln!(
                "[vivify] cands={} props={} otf_subsumed={}",
                snapshot.len(),
                self.stats.propagations.saturating_sub(start_props),
                self.stats.subsumed_removed.saturating_sub(start_subsumed),
            );
        }
        // The shared version deliberately leaves the trail at the last
        // candidate's end state for reuse; this round is over, so restore
        // the level-0 invariant the surrounding inprocessing passes assume.
        self.backtrack(0);

        // The probe loop above drained any still-pending level-0 propagation
        // queue under probe decision levels and threw the resulting
        // assignments away on backtrack.  Rewind the head so the next
        // `propagate()` re-derives the level-0 consequences that were lost.
        // (Ported from upstream v0.3.3.)
        self.trail.reset_propagation_head();
    }

    /// Vivify one candidate reusing the still-live decision prefix of the
    /// previous candidate (POS'25 trie-shared decisions; see
    /// `vivify_clauses`).  `prev_lits`/`prev_depths` describe the previous
    /// candidate's examined-literal prefix: `prev_depths[j]` is the exact
    /// decision depth (relative to the round's base level) after handling
    /// `prev_lits[..=j]`.  The trail still holds that state — identical
    /// decision sequences propagate identically, so starting the scan at
    /// the first diverging index is exactly the state a fresh scan would
    /// have reached there.
    ///
    /// **Exact depths are a soundness requirement, not an optimization**: a
    /// later candidate that backtracks to an interpolated (too-deep) level
    /// inherits the previous candidate's extra decisions below the reuse
    /// point, and a conflict derived under those extra decisions does not
    /// justify the recorded strengthening (caught in development as a 3.3x
    /// inflation of strengthenings; see the study).
    ///
    /// On return the trail holds THIS candidate's end state (for the next
    /// round's reuse) — the caller backtracks to the base level after the
    /// whole round, not per candidate.
    /// On-the-fly subsumption test (POS'25, cadical `vivify_deduce`'s
    /// `marked2` check): does clause `d_id` subsume the candidate `cand`
    /// modulo the level-0 units — i.e. is every literal of `d_id` either a
    /// literal of `cand` or permanently false at decision level 0?  Such a
    /// `d_id` entails `cand` outright (level-0-false literals are droppable
    /// from `d_id` under the units), so `cand` can be deleted.
    fn vivify_otf_subsumed(&self, cand: &[Lit], cid: ClauseId, d_id: ClauseId) -> bool {
        if crate::vivify_otf_disabled() {
            return false;
        }
        // cadical `assert (c != subsuming)`: the subsumer must differ from
        // the candidate.  The candidate CAN be its own conflict/reason
        // clause (assuming ¬ of a prefix propagates the rest of C), and
        // "C ⊆ C" would pass the subset test trivially — deleting C on its
        // own word, with nothing justifying the deletion.
        if d_id == cid {
            return false;
        }
        let Some(d) = self.clauses.get(d_id) else {
            return false;
        };
        if d.deleted {
            return false;
        }
        for &dl in d.lits {
            let val = self.trail.lit_value(dl);
            if val.is_false() && self.trail.level(dl.var()) == 0 {
                continue; // fixed-false: droppable modulo the units
            }
            if !cand.contains(&dl) {
                return false;
            }
        }
        true
    }

    fn vivify_clause_shared(
        &mut self,
        cid: ClauseId,
        lits: &[Lit],
        prev_lits: &mut SmallVec<[Lit; 8]>,
        prev_depths: &mut SmallVec<[u32; 8]>,
    ) -> bool {
        let base_level = self.trail.decision_level() - prev_depths.last().copied().unwrap_or(0);
        let n = lits.len();
        let mut shorten_to: Option<SmallVec<[Lit; 8]>> = None;
        // On-the-fly subsumption (POS'25 / cadical `vivify_deduce`): when
        // vivifying C finds a conflict or an implied literal whose reason
        // clause D satisfies `D \ {level-0-fixed literals} ⊆ C`, C is
        // DELETED as subsumed rather than shrunk — D ⊨ C outright.
        let mut subsumed_by: Option<ClauseId> = None;

        // Shared prefix: literal-index count whose handling is already live.
        // `prev_lits.len() == prev_depths.len()` holds by the lockstep
        // pushes below, so `prev_depths[shared - 1]` is always valid.
        let mut shared = 0usize;
        let cap = prev_lits.len().min(n);
        while shared < cap && prev_lits[shared] == lits[shared] {
            shared += 1;
        }
        // Backtrack ONLY to the divergence point (the decision depth that
        // corresponds to having handled `shared` literals).
        let keep_level = if shared == 0 {
            base_level
        } else {
            base_level + prev_depths[shared - 1]
        };
        self.backtrack(keep_level);

        let mut depths: SmallVec<[u32; 8]> = SmallVec::new();
        if shared > 0 {
            depths.extend_from_slice(&prev_depths[..shared]);
        }
        // One past the last literal actually examined this candidate.
        let mut handled_end = shared;

        'outer: for j in shared..n {
            match self.trail.lit_value(lits[j]) {
                crate::literal::LBool::True => {
                    // Satisfied from here; [0..=j] examined (j by this very
                    // check, no decision added — depth unchanged).
                    handled_end = j + 1;
                    depths.push(self.trail.decision_level() - base_level);
                    break 'outer;
                }
                crate::literal::LBool::False => {}
                crate::literal::LBool::Undef => {
                    self.trail.new_decision_level();
                    self.trail.assign_decision(lits[j].negate());
                    if let Some(conflict_id) = self.propagate() {
                        // Falsifying lits[0..=j] conflicts → prefix implied.
                        // But first: if the conflict clause itself subsumes
                        // C (all its literals in C or level-0-fixed), the
                        // whole clause goes, no shrink needed.
                        if self.vivify_otf_subsumed(lits, cid, conflict_id) {
                            subsumed_by = Some(conflict_id);
                        } else {
                            shorten_to = Some(lits[0..=j].iter().copied().collect());
                        }
                        handled_end = j + 1;
                        // Depth after handling j (the just-made decision);
                        // keep depths in lockstep with handled_end.
                        depths.push(self.trail.decision_level() - base_level);
                        break 'outer;
                    }
                }
            }
            // Did the propagation force a later clause literal true?
            // (lits[0..=j] ∨ lits[m]) is then implied.  When the implying
            // reason clause subsumes C outright, delete instead of shrink.
            for m in (j + 1)..n {
                if self.trail.lit_value(lits[m]).is_true() {
                    if let crate::trail::Reason::Propagation(rid) = self.trail.reason(lits[m].var())
                        && self.vivify_otf_subsumed(lits, cid, rid)
                    {
                        subsumed_by = Some(rid);
                    } else {
                        let mut s: SmallVec<[Lit; 8]> = lits[0..=j].iter().copied().collect();
                        s.push(lits[m]);
                        shorten_to = Some(s);
                    }
                    handled_end = j + 1;
                    depths.push(self.trail.decision_level() - base_level);
                    break 'outer;
                }
            }
            handled_end = j + 1;
            depths.push(self.trail.decision_level() - base_level);
        }

        // Publish the examined prefix and its exact depths (lockstep with
        // handled_end by construction above).
        *prev_lits = lits.iter().take(handled_end).copied().collect();
        *prev_depths = depths;

        // On-the-fly subsumption commit: mirror `subsume_round`'s rules —
        // promote a learned subsumer to original when the deleted clause is
        // original (else reduction could later drop the justification and
        // uncover a false SAT — the `crn_11_99_u` lesson), re-arm
        // elimination for the removed literals, retire, and account.
        if let Some(sub_id) = subsumed_by {
            let subsumed_learned = self.clauses.get(cid).is_some_and(|c| c.learned);
            if !subsumed_learned && self.clauses.get(sub_id).is_some_and(|s| s.learned) {
                self.clauses.clear_learned(sub_id);
            }
            if let Some(c) = self.clauses.get(cid) {
                let removed: SmallVec<[Lit; 8]> = c.lits.iter().copied().collect();
                self.mark_elim_vars(removed.iter().copied());
            }
            self.retire_clause(cid);
            self.stats.deleted_clauses += 1;
            self.stats.subsumed_removed += 1;
            return true;
        }

        let Some(new_lits) = shorten_to else {
            return false;
        };
        // Only replace if we actually shrank (and kept ≥ 2 literals: a unit /
        // empty clause from vivification needs separate handling we skip here).
        if new_lits.len() >= lits.len() || new_lits.len() < 2 {
            return false;
        }
        // Re-arm elimination for the shrunken clause's variables (cadical
        // marks on `shrink_clause`).
        self.mark_elim_vars(lits.iter().copied());
        self.replace_clause_lits(cid, &new_lits);
        true
    }

    /// Replace a clause's literals in place, re-attaching the two watched
    /// literals. (DRAT: the caller's context logs the strengthening; here we
    /// just keep the watched-literal invariant consistent.)
    fn replace_clause_lits(&mut self, cid: ClauseId, new_lits: &[Lit]) {
        // Detach old watches (on the current positions 0 and 1).
        let (old_w0, old_w1) = match self.clauses.get(cid) {
            Some(c) if !c.deleted && c.lits.len() >= 2 => (c.lits[0], c.lits[1]),
            _ => return,
        };
        self.watches.remove_clause(old_w0.negate(), cid);
        self.watches.remove_clause(old_w1.negate(), cid);

        // Pick the two best watch literals (prefer satisfied, then unassigned).
        let mut idxs: SmallVec<[usize; 8]> = (0..new_lits.len()).collect();
        idxs.sort_by(|&a, &b| {
            self.watch_rank(new_lits[b])
                .cmp(&self.watch_rank(new_lits[a]))
        });
        let (i0, i1) = (idxs[0], idxs[1]);

        {
            // Move the chosen watches to positions 0 and 1.
            let mut lits: SmallVec<[Lit; 8]> = new_lits.iter().copied().collect();
            lits.swap(0, i0);
            // i1 may have shifted if i1 == 0; recompute against the swapped vec.
            let i1 = if i1 == 0 {
                i0
            } else if i1 == i0 {
                0
            } else {
                i1
            };
            lits.swap(1, i1);
            self.clauses.shrink(cid, &lits);
            // An in-place shrink invalidates the stored LBD: the tier and the
            // `lbd <= len` invariant (checked by `check_learned_clause_lbd`)
            // are defined over the *stored* literals, so recompute it.  All
            // surviving literals are false on the trail at this moment
            // (vivification/strengthening only drops literals it proved
            // redundant), so the recomputation is well-defined.
            if self.clauses.get(cid).is_some_and(|c| c.learned) {
                let lbd = self.compute_lbd(&lits);
                self.clauses.set_lbd(cid, lbd);
                self.clauses.assign_tier_from_lbd(cid);
            }
            let w0 = lits[0];
            let w1 = lits[1];
            self.attach_watchers(cid, w0, w1);
        }
    }

    /// Run propagation capped at `limit` steps. Returns `(conflict, aborted)`:
    /// `aborted=true` means the step budget was hit before propagation finished
    /// – treat as "bail this probe" (neither a real conflict nor a complete
    /// model). Used by preprocessing passes (probing/vivify) so a single
    /// doomed cascade can't run unbounded (a ~7s slowdown on Urquhart).
    pub(super) fn propagate_bounded(&mut self, limit: u64) -> (bool, bool) {
        self.propagate_step_limit = Some(limit);
        self.propagate_aborted = false;
        let conflict = self.propagate().is_some();
        let aborted = self.propagate_aborted;
        self.propagate_step_limit = None;
        self.propagate_aborted = false;
        (conflict, aborted)
    }

    /// Failed-literal probing with on-the-fly hyper-binary resolution
    /// (cadical-style, simplified – no dominator LCA).
    ///
    /// Probe each still-unassigned literal `r` at decision level 1 and run BCP.
    ///   * If the probe conflicts, `r` is a *failed literal*: force `¬r` as a
    ///     level-0 unit (every model must set `r` false).
    ///   * If it does not conflict, every literal `q` forced during the probe by
    ///     a *non-binary* clause satisfies `r → q` (the clause became unit solely
    ///     because `r` made its other literals false), so the binary clause
    ///     `(¬r ∨ q)` is implied – add it as a learned binary (a hyper-binary
    ///     resolvent) when not already present. This enriches the binary
    ///     implication graph, making later propagation/probing stronger.
    ///
    /// Soundness: forced units and derived binaries are all consequences of the
    /// formula (BCP is sound and learned clauses are implied). Bounded by a
    /// deterministic propagation-step budget and a per-probe cap so it never
    /// dominates – not wall-clock (see `vivify_clauses`' budget note).
    pub(super) fn probe_hyper_binary(&mut self) -> (usize, usize) {
        if self.trail.decision_level() != 0 {
            return (0, 0);
        }
        const MAX_PROBE_PROPS: u64 = 10_000_000;
        const PER_PROBE_CAP: u32 = 20_000;
        let start_props = self.stats.propagations;
        let mut failed = 0usize;
        let mut hyper = 0usize;

        let n = self.num_vars;
        for i in 0..n {
            if self.trivially_unsat {
                break;
            }
            if self.stats.propagations.saturating_sub(start_props) > MAX_PROBE_PROPS {
                break;
            }
            let v = Var::new(i as u32);
            if self.trail.is_assigned(v) {
                continue;
            }
            let r = Lit::pos(v);

            self.trail.new_decision_level();
            self.trail.assign_decision(r);
            let (conflict, aborted) = self.propagate_bounded(PER_PROBE_CAP.into());
            if conflict {
                self.backtrack(0);
                self.force_level0(r.negate());
                failed += 1;
            } else if aborted {
                // Cascade hit the step cap – densely constrained, skip.
                self.backtrack(0);
            } else {
                self.derive_hyper_binaries(r, &mut hyper);
                self.backtrack(0);
            }
        }
        (failed, hyper)
    }

    /// Add `(¬r ∨ q)` as a learned binary for every literal `q` forced during the
    /// probe of `r` whose reason is a non-binary clause (the hyper-binary case).
    pub(super) fn derive_hyper_binaries(&mut self, r: Lit, hyper: &mut usize) {
        // Walk the literals assigned at the probe level (level >= 1) with a
        // propagation reason; the probe literal itself is a decision, skipped.
        let probe_lits: SmallVec<[Lit; 64]> = self.trail.level_assignments().to_vec().into();
        let mut added = 0u32;
        for q in probe_lits {
            if added >= 64 {
                break; // cap binaries derived per probe to limit clutter
            }
            let Reason::Propagation(cid) = self.trail.reason(q.var()) else {
                continue;
            };
            // Only derive from non-binary reasons (binary reasons are already edges).
            let is_long = self.clauses.get(cid).is_some_and(|c| c.lits.len() > 2);
            if !is_long {
                continue;
            }
            // r → q already? (binary (¬r ∨ q) present)
            if self.has_binary_implication(r, q) {
                continue;
            }
            let id = self.clauses.add_learned([r.negate(), q]);
            // Set the LBD this hyper-binary-resolution clause actually has.
            // Every other `add_learned` site computes and stores it (see the
            // sibling HBR path in `propagate.rs` and its design note: a stuck
            // LBD of 0 at `Clause::learned`'s default gave every HBR clause an
            // artificially easy path into permanent Core retention via
            // `record_usage`'s `lbd <= 2` promote, regardless of quality).
            // This site used to be the exception – the LBD-0 invariant
            // (debug) caught it on the pigeonhole case.
            let lbd = self.compute_lbd(&[r.negate(), q]);
            self.clauses.set_lbd(id, lbd);
            self.debug_check_learned_clause_lbd(id);
            // BIG registration (and the phantom tick count) happens inside
            // `attach_watchers` for binaries.
            self.attach_watchers(id, r.negate(), q);
            self.clause_hyper.resize(id.index() + 1, false);
            self.clause_hyper[id.index()] = true;
            *hyper += 1;
            added += 1;
        }
    }

    /// Failed-literal probing (at decision level 0).
    ///
    /// For each unassigned variable, tentatively assign each polarity and run
    /// unit propagation. If a probe leads to a conflict, the opposite polarity
    /// is implied by the current level-0 facts, so we add it as a permanent
    /// level-0 unit and propagate. This deduces forced assignments that plain
    /// unit propagation cannot – it is the technique that lets cadical solve
    /// structured instances such as `simon` with zero search decisions. Bounded
    /// by a propagation budget so it never dominates on huge instances.
    ///
    /// Returns the number of units forced this round.
    pub(super) fn failed_literal_probing(&mut self) -> usize {
        if self.trail.decision_level() != 0 {
            return 0;
        }

        // Propagation budget for the whole pass. The old `num_vars*8` value
        // (~62K props on longmult15) allowed barely a single probe before
        // bailing, so probing was effectively a no-op even with `INPROCESS=1`.
        // A full failed-literal pass is ~2*num_vars probes; on the binary-heavy
        // structured instances it targets, BCP is cheap, so allow a generous
        // fraction of a full sweep.
        let budget = (self.num_vars.saturating_mul(512)).max(50_000) as u64;
        let start_props = self.stats.propagations;
        let mut forced = 0usize;

        // Snapshot the currently-unassigned variables (probing forces some).
        let vars: SmallVec<[Var; 64]> = (0..self.num_vars as u32).map(Var::new).collect();

        for &v in &vars {
            if self.trivially_unsat {
                break;
            }
            if self.stats.propagations.saturating_sub(start_props) > budget {
                break;
            }
            if self.trail.is_assigned(v) {
                continue;
            }

            // Probe positive polarity.
            if self.probe_conflicts(Lit::pos(v)) {
                self.force_level0(Lit::neg(v));
                forced += 1;
                continue;
            }
            // Probe negative polarity.
            if self.probe_conflicts(Lit::neg(v)) {
                self.force_level0(Lit::pos(v));
                forced += 1;
            }
        }

        // Every `probe_conflicts` above opened a decision level, propagated
        // (draining any still-pending level-0 literals *at the probe level*)
        // and backtracked, discarding the consequences.  Rewind so the next
        // `propagate()` re-derives the lost level-0 implications — the same
        // hanging-unit repair as `vivify_clauses`. (Ported from upstream
        // v0.3.3.)
        self.trail.reset_propagation_head();
        forced
    }

    /// Probe a single literal: assign it at a fresh decision level, propagate,
    /// then undo. Returns true if the probe conflicted (the literal is false).
    fn probe_conflicts(&mut self, lit: Lit) -> bool {
        self.trail.new_decision_level();
        self.trail.assign_decision(lit);
        let (conflict, _aborted) = self.propagate_bounded(50_000);
        self.backtrack_with_phase_saving(0);
        conflict
    }

    /// Force a literal as a permanent level-0 fact and propagate. Assumes we
    /// are at decision level 0. Sets `trivially_unsat` if it conflicts.
    pub(super) fn force_level0(&mut self, lit: Lit) {
        use crate::literal::LBool;
        match self.trail.lit_value(lit) {
            LBool::True => return,
            LBool::False => {
                self.trivially_unsat = true;
                return;
            }
            LBool::Undef => {}
        }
        self.trail.assign_decision(lit);
        if self.propagate().is_some() {
            self.trivially_unsat = true;
        }
    }

    /// Perform inprocessing (apply preprocessing during search)
    pub(super) fn inprocess(&mut self) {
        use crate::Preprocessor;

        // Only inprocess at decision level 0. LRAT tracing steps aside entirely:
        // `strengthen_clauses_inprocessing`'s redundant-literal check derives its
        // shorter clause via a hypothetical assign-and-propagate probe this
        // module does not thread a hint chain through (and the subsumption /
        // pure-literal-elimination passes rewrite the live clause set in ways the
        // tracer cannot back with sound addition/deletion lines), so rather than
        // emit proof steps this port cannot justify, the whole pass is skipped
        // while an LRAT tracer is attached. Faithful port of v0.3.2's
        // `|| self.lrat.is_some()` gate (main's `lrat` is a `bool`).
        if self.trail.decision_level() != 0 || self.lrat {
            return;
        }

        // Pass-attribution telemetry (2026-09-04 gating follow-up): snapshot
        // the per-pass cumulative counters around each pass so the round trace
        // can attribute cost/yield to the component that produced it.  Purely
        // diagnostic; see `inproc_round_trace_enabled`.
        let t = inproc_round_trace_enabled();
        let els0 = t.then_some(self.stats.substitutions);
        let units0 = t.then_some(self.stats.unit_clauses);
        let shr0 = t.then_some(self.stats.shrunken);
        let sub0 = t.then_some(self.stats.subsumed_removed + self.stats.self_subsumed);
        // Per-pass COST attribution (2026-09-07): propagation spent inside
        // each pass, so the round trace can separate vivify's cost from
        // subsumption's.  Propagation is the dominant round cost on the
        // corpus (occurrence scans barely propagate); diagnostic only.
        let els_p0 = t.then_some(self.stats.propagations);

        // Equivalent-literal substitution round (cadical interleaves its
        // `decompose`/`sweep`-class ELS inside the inprocessing schedule).
        // The round variant skips the pre-search one-shot latch – the
        // substitution map composes across rounds – while keeping every
        // soundness gate (level 0, base scope, no proof tracing). Skipped
        // under a real theory for the same reason as the pure-literal pass
        // below: theory lemmas can force the opposite polarity of a
        // Boolean-pure variable, and folding it mid-search desyncs the
        // theory's atom view.
        if self.config.enable_equiv_substitution && self.destructive_preprocessing_safe() {
            if self.substitute_equivalent_literals_round() == equiv::SubstOutcome::Unsat {
                self.trivially_unsat = true;
                return;
            }
            if self.trivially_unsat {
                return;
            }
        }

        // Mid-search structured BVA (kissat `factor`-class component; see
        // `solver/bva.rs`): introduce aux vars merging original-clause
        // groups under the round's effort budgets.  Runs BEFORE the
        // pure-literal/subsume passes so they see (and can consume) the
        // introduced structure — and BEFORE the `Preprocessor` is sized,
        // since introductions grow the variable space its occurrence
        // arrays are indexed by.  Introductions leave watches/BIG stale
        // and can add level-0 units ((G ∨ t) with G fully false forces t,
        // then each (¬t ∨ U_i) forces U_i) — rebuild and re-propagate
        // immediately; a conflict there is a genuine Unsat certificate
        // over live clauses.
        //
        // Per-pass cost attribution: BVA pass marker (also closes the ELS
        // slot: its delta is the props spent above).
        let mut diag_props = [0u64; 5];
        if let Some(p) = els_p0 {
            diag_props[0] = self.stats.propagations.saturating_sub(p);
        }
        let bva_p0 = t.then_some(self.stats.propagations);
        let mut introduced_now = 0usize;
        if self.config.enable_mid_bva {
            let (n, _saved) = self.structured_bva_mid();
            introduced_now += n;
        }
        if self.config.enable_mid_andgate {
            introduced_now += self.and_gate_factoring_mid();
        }
        if introduced_now > 0 {
            self.rebuild_watches_and_binary_graph();
            if self.propagate().is_some() {
                // Level-0 conflict from the re-encoded clauses: the
                // original formula was already falsified by the
                // level-0 trail (the encodings' old→new directions make
                // this sound — see `solver/bva.rs`).
                self.trivially_unsat = true;
                return;
            }
        }
        if let Some(p) = bva_p0 {
            diag_props[1] = self.stats.propagations.saturating_sub(p);
        }

        // Create preprocessor with the CURRENT number of variables —
        // after BVA, which may have introduced new ones.
        let mut preprocessor = Preprocessor::new(self.num_vars);
        // Per-pass cost attribution: pure-literal + subsume pass marker.
        let puresub_p0 = t.then_some(self.stats.propagations);
        // Snapshot every live clause's literals before the elimination passes
        // below run. `Preprocessor::pure_literal_elimination` and
        // `subsumption_elimination` retire clauses by setting `Clause::deleted`
        // directly on `self.clauses` (they don't go through
        // `ClauseDatabase::remove`) and report only a count, not which ids were
        // touched. `drat_delete(id)` can't be used afterwards either – by
        // design it refuses to read literals off a clause already marked
        // deleted, to avoid ever emitting a deletion line with garbage
        // literals. Without this snapshot the deletions below would never
        // reach the DRAT proof: the checker would still accept the proof (an
        // omitted deletion hint only makes it larger, never invalid), but the
        // proof would keep clauses the live database no longer has, which is
        // exactly the minimality gap this snapshot closes. Skipped entirely
        // when proof logging is off.
        let _pre_lits: Vec<(ClauseId, SmallVec<[Lit; 8]>)> = if self.proof.is_some() {
            self.clauses
                .iter_ids()
                .filter_map(|id| {
                    self.clauses
                        .get(id)
                        .map(|c| (id, c.lits.iter().copied().collect()))
                })
                .collect()
        } else {
            Vec::new()
        };
        // Id-only pre-state for the reason/edge hygiene pass below (always
        // taken, unlike the DRAT literal snapshot): literals survive the
        // deleted flag, so post-pass bookkeeping can read them from the
        // database directly.
        let pre_live_ids: Vec<ClauseId> = self.clauses.iter_ids().collect();

        // Pure-literal elimination deletes original clauses; that is only
        // satisfiability-preserving if the pure literal is fixed to its polarity
        // in the reconstructed model. It is also unsound across incremental
        // scopes, where a later `add_clause` could reintroduce the opposite
        // polarity after the clauses were dropped, so it is only run at the base
        // assertion level (no active `push`). It is likewise unsound while a
        // *real* theory callback is attached: theory lemmas and propagations can
        // force the opposite polarity of a variable with one-sided Boolean
        // occurrences, and `save_model` would pin the pure polarity regardless
        // (see `TheoryCallback::is_real_theory`).
        if self.assertion_levels.len() <= 1 && self.destructive_preprocessing_safe() {
            // Variables already fixed on the level-0 trail must be excluded
            // from pure-literal elimination (see
            // `Preprocessor::pure_literal_elimination`).
            let assigned: Vec<bool> = (0..self.num_vars)
                .map(|i| {
                    self.trail.is_assigned(Var::new(i as u32))
                        // Freeze set: theory-mapped variables never
                        // pure-eliminated (their polarity belongs to the
                        // theory, not to one-sided Boolean occurrence).
                        || self.frozen_vars.contains(&Var::new(i as u32))
                })
                .collect();
            let _pure_elim = preprocessor.pure_literal_elimination(&mut self.clauses, &assigned);
            // Record each eliminated pure literal so `save_model` can fix it to
            // `true`, keeping the deleted clauses satisfied even if the search
            // later assigns the variable the opposite phase. Keep at most one
            // polarity per variable (the first recorded).
            for &lit in preprocessor.eliminated_pure_literals() {
                let already = self
                    .pure_literal_reconstruction
                    .iter()
                    .any(|existing| existing.var() == lit.var());
                if !already {
                    self.pure_literal_reconstruction.push(lit);
                }
            }
        }

        // Emit a DRAT deletion line for every clause the pure-literal pass
        // above retired, identified by diffing against the pre-pass snapshot
        // (any previously-live clause that is now deleted).
        let mut newly_deleted: Vec<(ClauseId, SmallVec<[Lit; 8]>)> = Vec::new();
        for id in &pre_live_ids {
            if self.clauses.get(*id).is_some_and(|c| c.deleted)
                && let Some(c) = self.clauses.get(*id)
            {
                newly_deleted.push((*id, c.lits.iter().copied().collect()));
            }
        }
        for (id, lits) in &newly_deleted {
            {
                // The pure-literal pass deleted inside a bare
                // `&mut ClauseDatabase` (no trail access), so re-point any
                // live reason reference here, Solver-side: a deleted clause
                // can still be the recorded propagation reason of an
                // assigned literal (binary reasons escape the `lits[0]`
                // invariant). `Decision` is exact for level-0 facts.
                for &l in lits {
                    let var = l.var();
                    if self.trail.is_assigned(var)
                        && matches!(
                            self.trail.reason(var),
                            Reason::Propagation(r) if r == *id
                        )
                    {
                        self.trail.set_reason(var, Reason::Decision);
                    }
                }
                // Purge the deleted binary's implication-graph edges (the
                // Preprocessor deleted inside a bare `&mut ClauseDatabase`,
                // so `retire_clause`'s purge never ran): a stale edge keeps
                // PROPAGATING (the binary loop does not consult the deleted
                // flag) and re-records reasons pointing at the deleted
                // clause. The snapshot lits are exactly what
                // `purge_binary_edges` needs.
                if lits.len() == 2 {
                    let (a, b) = (lits[0], lits[1]);
                    self.binary_graph.remove_clause_edges(a.negate(), *id);
                    self.binary_graph.remove_clause_edges(b.negate(), *id);
                }
                self.drat_delete_lits(lits);
            }
        }

        // Forward subsumption + self-subsuming strengthening over the *whole*
        // live database (originals and keep-worthy learned clauses), ported
        // from cadical `subsume.cpp`: occurrence-driven, size-ordered,
        // budget-bounded.  The previous pairwise scan was O(N²·L²) over
        // originals only and too slow to schedule mid-search at all, which is
        // why cadical's 46 %-subsumed-clauses behaviour on inprocessing-heavy
        // instances (`stable-300-0.1-20`) never materialized here.  The
        // probe-based `strengthen_clauses_inprocessing` is subsumed by the
        // strengthening half of this round (and was capped at 50 clauses).
        let (_subsumed, _strengthened) = self.subsume_round();

        // Per-pass cost attribution: vivify pass marker (closes pure+sub).
        if let Some(p) = puresub_p0 {
            diag_props[2] = self.stats.propagations.saturating_sub(p);
        }
        let viv_p0 = t.then_some(self.stats.propagations);

        // Vivification round (cadical schedules `vivify` inside its
        // inprocessing rounds): shortens both learned and – when no proof is
        // attached – original clauses. The shortened clauses re-arm
        // elimination (their variables are marked in `vivify_clause`).
        self.vivify_clauses();

        // Per-pass cost attribution: transred pass marker (closes vivify).
        if let Some(p) = viv_p0 {
            diag_props[3] = self.stats.propagations.saturating_sub(p);
        }
        let tred_p0 = t.then_some(self.stats.propagations);

        // Transitive reduction of the binary implication graph (cadical
        // schedules `transred` inside `inprobe`; the documented amortizer
        // for hyper-binary resolution). Original binaries are only ever
        // retired via original-only alternative paths; failed literals
        // surface as forced level-0 units.
        let (_tred, _tfailed) = self.transred_round();
        if let Some(p) = tred_p0 {
            diag_props[4] = self.stats.propagations.saturating_sub(p);
        }

        // Stash the per-pass deltas for the round-site trace (telemetry).
        if let (Some(e0), Some(u0), Some(s0), Some(b0)) = (els0, units0, shr0, sub0) {
            self.inproc_diag = [
                self.stats.substitutions - e0,
                self.stats.unit_clauses - u0,
                self.stats.shrunken - s0,
                (self.stats.subsumed_removed + self.stats.self_subsumed) - b0,
                _tred as u64,
                _tfailed as u64,
            ];
            self.inproc_diag_props = diag_props;
        }

        // Re-arm unit propagation over the whole surviving trail.
        //
        // This is not an optimization guard, it repairs a real completeness
        // hole.  `inprocess` runs right after conflict handling in the search
        // loop, at which point the level-0 propagation queue is routinely
        // *non-empty*.  `vivify_clauses` and the probe passes above open
        // probe decision levels, assign literals speculatively and call
        // `propagate()` — which drains the still-pending level-0 literals
        // under the probe's assumptions: any consequence it derives is filed
        // at the probe level, and the subsequent backtrack throws those
        // consequences away.  The genuine level-0 implications among them are
        // then never re-derived — leaving a live clause with one unassigned
        // literal and every other literal false that nothing will ever fire
        // on (a "hanging unit").  In-place strengthening
        // (`remove_literal_and_rewatch`) has the same shape and rewinds at
        // its own site.  Rewinding the head makes the next `propagate()`
        // rescan the whole trail and re-derive every lost level-0
        // consequence; re-propagating an already-assigned literal is a no-op.
        // (Ported from upstream v0.3.3.)
        self.trail.reset_propagation_head();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Regression test for the `inprocess()` DRAT-deletion gap: pure-literal
    /// elimination and subsumption elimination retire original clauses
    /// directly on the clause database (setting `Clause::deleted` without
    /// going through `ClauseDatabase::remove`), and every clause they retire
    /// must show up as a `d`-line in the DRAT proof – not just the separate
    /// on-the-fly-strengthening path (`remove_literal_and_rewatch`), which
    /// already logged correctly before this fix.
    #[test]
    fn inprocess_drat_deletion_count_matches_removed_clauses() {
        let path = std::env::temp_dir().join("nixie_sat_inprocess_drat_deletion_count.drat");

        let mut solver = Solver::new();
        let y = solver.new_var();
        let w1 = solver.new_var();
        let w2 = solver.new_var();
        let p = solver.new_var();
        let q = solver.new_var();
        let r = solver.new_var();

        // Pure-literal family: `y` occurs only positively, across two
        // clauses that must both be deleted by `pure_literal_elimination`.
        solver.add_clause([Lit::pos(y), Lit::pos(w1)]);
        solver.add_clause([Lit::pos(y), Lit::pos(w2)]);

        // Subsumption pair: (p ∨ q) subsumes (p ∨ q ∨ r), so the latter must
        // be deleted by `subsumption_elimination`.
        solver.add_clause([Lit::pos(p), Lit::pos(q)]);
        solver.add_clause([Lit::pos(p), Lit::pos(q), Lit::pos(r)]);

        // Decoy giving w1, w2, p, q, r an opposite-polarity occurrence each,
        // so none of them is independently pure (only `y` is) – this keeps
        // the (p ∨ q ∨ r) deletion attributable to subsumption alone rather
        // than being pre-empted by pure-literal elimination on `r`.
        solver.add_clause([
            Lit::neg(w1),
            Lit::neg(w2),
            Lit::neg(p),
            Lit::neg(q),
            Lit::neg(r),
        ]);

        solver
            .enable_drat_proof(&path)
            .expect("enable DRAT proof logging");

        // `inprocess` only acts at decision level 0, which a freshly built
        // solver already is.
        assert_eq!(solver.trail.decision_level(), 0);
        let live_before: Vec<ClauseId> = solver.clauses.iter_ids().collect();

        solver.inprocess();

        let removed: Vec<ClauseId> = live_before
            .into_iter()
            .filter(|&id| solver.clauses.get(id).is_some_and(|c| c.deleted))
            .collect();
        assert_eq!(
            removed.len(),
            3,
            "expected exactly 3 clauses removed (2 pure-literal + 1 subsumed)"
        );

        solver.disable_drat_proof();

        let contents = std::fs::read_to_string(&path).expect("read DRAT proof file");
        std::fs::remove_file(&path).ok();

        let deletion_lines = contents
            .lines()
            .filter(|line| line.trim_start().starts_with("d "))
            .count();

        assert_eq!(
            deletion_lines,
            removed.len(),
            "DRAT deletion-line count must match the number of clauses inprocess() removed"
        );
    }
}

/// On-the-fly subsumption self-guard (POS'25 port): assuming the
/// negation of a clause prefix can make the candidate clause C its own
/// propagation reason or conflict clause (e.g. C = (a ∨ b ∨ c) under
/// decisions ¬a, ¬b propagates c with reason C).  The subset test
/// "D ⊆ C" then holds trivially for D = C, and deleting C on its own
/// word is a false deletion with no justification — measured live: it
/// flipped `6s167-opt` to a false `sat` (cadical: `unsat`) before the
/// guard.  cadical's `assert (c != subsuming)` is the same rule.
#[test]
fn vivify_otf_subsumption_rejects_self() {
    let mut solver = Solver::new();
    let a = solver.new_var();
    let b = solver.new_var();
    let c = solver.new_var();
    // C = (a ∨ b ∨ c) and a distinct smaller clause D = (a ∨ b).
    let big = solver
        .clauses
        .add_original([Lit::pos(a), Lit::pos(b), Lit::pos(c)]);
    let small = solver.clauses.add_original([Lit::pos(a), Lit::pos(b)]);
    let cand: SmallVec<[Lit; 8]> = [Lit::pos(a), Lit::pos(b), Lit::pos(c)]
        .into_iter()
        .collect();
    // Self: must be rejected even though the subset test passes
    // trivially.
    assert!(!solver.vivify_otf_subsumed(&cand, big, big));
    // A genuine subsumer (at level 0, nothing fixed) is accepted.
    assert!(solver.vivify_otf_subsumed(&cand, big, small));
}
