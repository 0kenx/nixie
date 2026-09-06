//! Global forward subsumption with strengthening (port of CaDiCaL `subsume.cpp`).
//!
//! For every scheduled clause `c` (ascending size) we look for an already
//! *connected* clause `d` (smaller or equal size) whose literals all occur in
//! `c` – then `c` is subsumed and deleted – or that occur in `c` except for
//! exactly one complementary literal – then that literal is removed from `c`
//! (self-subsuming resolution).  After a clause has been checked (and neither
//! subsumed nor strengthened) it is *connected* into the one-watched
//! occurrence list of its least-occurring literal, so later (larger)
//! candidates can find it as a subsumer.
//!
//! This replaces the previous O(N²·L²) pairwise scan
//! (`Preprocessor::subsumption_elimination`), which could not be scheduled
//! mid-search at all: on `stable-300-0.1-20` (17.5k clauses) one round of it
//! exceeded any reasonable conflict interval, while CaDiCaL runs an
//! occurrence-driven round every ~2k conflicts and credits it with 46 %
//! subsumed clauses on that instance.
//!
//! Differences from CaDiCaL, deliberately:
//! * no `subsume` dirty-bit filtering of which clauses need re-checking
//!   (rebuild the schedule every round; the budget bounds the work);
//! * binaries are matched through the existing [`BinaryImplicationGraph`]
//!   instead of CaDiCaL's dedicated per-literal arrays;
//! * no `transred` (transitive reduction of the binary implication graph).
//!
//! Runs at decision level 0 only, like every inprocessing pass.

use super::*;
use crate::clause::{ClauseId, ClauseTier};

/// The subsume round's scheduling mode.
///
/// * `0` — full scan every round (the legacy schedule): every live clause
///   scheduled, every literal scanned, every checked clause connected.
/// * `1` — cadical's dirty-literal schedule: clauses with >= 2 literals
///   flagged dirty (touched by additions/strengthenings since the last
///   round) are candidates; checks scan only dirty literals; only
///   all-dirty clauses connect.
/// * `2` — **randomized partial subsumption (the default since
///   2026-09-07)**: identical machinery, but the flagged set is a fresh
///   random slice of the literal space each round (same size as the
///   natural marking rate).  Measured on the 54-file corpus x 5 seeds
///   (`docs/studies/2026-09-07-inproc-effort-schedule.md`): conflicts
///   geomean **0.908x vs full** and wall **0.910x** (the recency arm
///   measured 1.08x — T/N 1.153, the recency semantic is negative at our
///   round cadence), P(solve) 179 vs 176, 0 verdict mismatches over 1060
///   cells.  Mechanism: rotating partial hygiene — coverage cycles
///   through the whole database without re-checking known-clean pairs
///   (full scan's waste) and without recency's systematic blind spots.
///
/// `NIXIE_SUBSUME2=0|1|2` selects (record-compatibility: the historical
/// `NIXIE_SUBSUME2_NULL=1` maps to mode 2).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum SubsumeScheduleMode {
    Full,
    Recency,
    RandomSlice,
}

#[cfg(feature = "std")]
pub(super) fn subsume2_mode() -> SubsumeScheduleMode {
    use std::sync::OnceLock;
    static FLAG: OnceLock<SubsumeScheduleMode> = OnceLock::new();
    *FLAG.get_or_init(|| {
        if let Ok(v) = std::env::var("NIXIE_SUBSUME2") {
            match v.as_str() {
                "0" => return SubsumeScheduleMode::Full,
                "1" => return SubsumeScheduleMode::Recency,
                "2" => return SubsumeScheduleMode::RandomSlice,
                _ => {}
            }
        }
        if subsume2_null() || subsume2_fullk() > 0 || subsume2_hotp() > 0 {
            return SubsumeScheduleMode::Recency;
        }
        SubsumeScheduleMode::RandomSlice
    })
}

#[cfg(not(feature = "std"))]
pub(super) fn subsume2_mode() -> SubsumeScheduleMode {
    SubsumeScheduleMode::Full
}

/// Matched null for the dirty schedule (env `NIXIE_SUBSUME2_NULL=1`,
/// implies the schedule): at each round end the dirty set is REPLACED by
/// the same number of codes drawn uniformly over the literal space
/// (deterministic xorshift) instead of cleared — identical schedule
/// magnitudes and timing, the correlation with "touched since the last
/// round" severed.  If the treatment's recency signal carries the value,
/// treatment < null; under chaos they are indistinguishable.
/// Periodic full-scan rounds (env `NIXIE_SUBSUME2_FULLK=K`, implies the
/// schedule): every K-th subsume round schedules and connects EVERYTHING
/// (the legacy full scan), restoring old-vs-old DB hygiene on an
/// amortized clock.  cadical relies on round rarity for this; our rounds
/// are frequent, so continuous hygiene needs the explicit full pass.
#[cfg(feature = "std")]
pub(super) fn subsume2_fullk() -> u64 {
    use std::sync::OnceLock;
    static FLAG: OnceLock<u64> = OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("NIXIE_SUBSUME2_FULLK")
            .ok()
            .and_then(|v| v.parse().ok())
            .filter(|k| *k >= 1)
            .unwrap_or(0)
    })
}

#[cfg(not(feature = "std"))]
pub(super) fn subsume2_fullk() -> u64 {
    0
}

/// Hot-literal probabilistic connect (env `NIXIE_SUBSUME2_HOTP=permille`,
/// implies the schedule): a clause that is NOT all-dirty connects with
/// probability p — on the least-occurring AMONG ITS DIRTY literals, so it
/// is discoverable exactly by the candidates plausibly containing it
/// (candidates scan only dirty literals; a clean-literal watch would be
/// invisible).  Bounded occs growth: p x (clauses with hot literals).
#[cfg(feature = "std")]
pub(super) fn subsume2_hotp() -> u64 {
    use std::sync::OnceLock;
    static FLAG: OnceLock<u64> = OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("NIXIE_SUBSUME2_HOTP")
            .ok()
            .and_then(|v| v.parse().ok())
            .filter(|p| *p > 0 && *p <= 1000)
            .unwrap_or(0)
    })
}

#[cfg(not(feature = "std"))]
pub(super) fn subsume2_hotp() -> u64 {
    0
}

#[cfg(feature = "std")]
pub(super) fn subsume2_null() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("NIXIE_SUBSUME2_NULL")
            .is_ok_and(|v| v == "1" || v.eq_ignore_ascii_case("true"))
    })
}

#[cfg(not(feature = "std"))]
pub(super) fn subsume2_null() -> bool {
    false
}

/// Trace flag for the dirty-schedule diagnostics (`NIXIE_SUB2_TRACE`).
#[cfg(feature = "std")]
pub(super) fn subsume_round_trace_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("NIXIE_SUB2_TRACE").is_ok())
}

#[cfg(not(feature = "std"))]
pub(super) fn subsume_round_trace_enabled() -> bool {
    false
}

/// Solver-level scratch for `subsume_round` (reused across rounds; see
/// `Solver::subsume_scratch`).  Plain data — taken/replaced wholesale via
/// `mem::take` so the pass body keeps disjoint-local borrows.
#[derive(Default, Clone, Debug)]
pub(crate) struct SubsumeScratch {
    pub(super) schedule: Vec<(u32, ClauseId)>,
    pub(super) occs: Vec<SmallVec<[ClauseId; 4]>>,
    pub(super) mark: Vec<i8>,
}

/// Outcome of one subsumption check of candidate `c` against connected `d`.
enum SubCheck {
    /// Every literal of `d` occurs in `c`: `c` is subsumed by `d`.
    Subsumed { subsumer: ClauseId },
    /// All but one literal of `d` occur in `c`, and that one occurs
    /// complemented: remove `remove` from `c` (self-subsuming resolution).
    /// `subsumer` carries the resolving clause's id — under an attached
    /// proof the strengthened clause's RUP chain is the resolution pair
    /// `[c, subsumer]` (see the strengthen arm below).
    Strengthen { remove: Lit, subsumer: ClauseId },
}

impl Solver {
    /// One forward-subsumption round over the live clause database.
    ///
    /// Returns `(subsumed, strengthened)` counts.  Sound at any assertion
    /// scope (a subsumed clause is entailed by its subsumer; a strengthened
    /// clause is entailed by resolution), but only runs at decision level 0.
    /// Proof-complete since 2026-09: deletions carry the subsumed clause's
    /// LRAT id, and each self-subsuming strengthen emits the resolution
    /// pair `[c, subsumer]` as the new clause's RUP chain (under `¬kept`
    /// every `subsumer` literal except the flipped one is false, so the
    /// subsumer is unit on it, propagating it and falsifying `c`).
    pub(super) fn subsume_round(&mut self) -> (usize, usize) {
        if self.trail.decision_level() != 0 || self.trivially_unsat {
            return (0, 0);
        }

        // Budget (cadical `subsumelimited`): delta = search propagations ×
        // subsumeeffort/1000 (= ×1), clamped to [2·active vars, 1e8] checks.
        // Effort-scheduled rounds (2026-09-07) use the cadical reference
        // exactly: cumulative SEARCH propagation (round-internal propagation
        // excluded via `inproc_round_props_total`), clamped
        // [subsumemineff=1e6, subsumemaxeff=1e9].
        let budget: u64 = if self.inproc_budgets.window > 0 {
            self.inproc_budgets.subsume_checks
        } else {
            self.stats
                .propagations
                .clamp((2 * self.num_vars.max(1)) as u64, 100_000_000)
        };
        let mut subchecks: u64 = 0;

        // Reused scratch (2026-09-07 amortization): the per-round fresh
        // `vec![SmallVec::new(); 2*num_vars]` + mark vec were a ~90 MB
        // alloc/free per round on big-DB instances - the dominant round
        // wall cost (measured 78 ms/round on g2-slp).  Same contents, same
        // order: trajectory-identical by construction.
        let mut sched = std::mem::take(&mut self.subsume_scratch.schedule);
        let mut occs = std::mem::take(&mut self.subsume_scratch.occs);
        let mut mark = std::mem::take(&mut self.subsume_scratch.mark);
        sched.clear();
        self.subsume_rounds_done = self.subsume_rounds_done.wrapping_add(1);
        let mode = subsume2_mode();
        let mut dirty = mode != SubsumeScheduleMode::Full;
        let fullk = subsume2_fullk();
        if fullk > 0 && self.subsume_rounds_done.is_multiple_of(fullk) {
            dirty = false; // periodic full-scan hygiene round
        }
        let num_lits = 2 * self.num_vars;
        if self.subsume_dirty.len() < num_lits {
            self.subsume_dirty.resize(num_lits, false);
        }
        if occs.len() == num_lits {
            for e in occs.iter_mut() {
                e.clear();
            }
        } else {
            occs.clear();
            occs.resize_with(num_lits, SmallVec::new);
        }
        if mark.len() != num_lits {
            mark.clear();
            mark.resize(num_lits, 0);
        }
        // (A same-length `mark` needs no clearing: the per-candidate unmark
        // discipline leaves every entry zero at every exit.)

        // Snapshot the schedule: live clauses within the size limit and with
        // no level-0-fixed literal, sorted ascending by size so smaller
        // (potential subsumers) are connected first.
        const CLS_LIMIT: usize = 100; // cadical subsumeclslim
        let mut has_candidate = false;
        for cid in self.clauses.iter_ids() {
            let Some(c) = self.clauses.get(cid) else {
                continue;
            };
            if c.deleted || c.lits.len() > CLS_LIMIT || c.lits.len() < 3 {
                continue;
            }
            // Learned clauses: only those worth keeping participate (cadical
            // `likely_to_be_kept_clause`): Core/Mid tier or low glue.  Local
            // tier (deleted en masse at every reduction) is not worth the
            // scheduling cost.
            if c.learned && matches!(c.tier, ClauseTier::Local) && c.lbd > 8 {
                continue;
            }
            // Skip clauses with a level-0 assigned literal: they are either
            // satisfied (nothing to do) or falsified-to-a-suffix (handled by
            // propagation), and skipping keeps the check assignment-free.
            if c.lits.iter().any(|&l| self.trail.lit_val(l) != 0) {
                continue;
            }
            // cadical dirty scheduling: a clause can only be subsumed by a
            // NEW clause d (occs hold only all-dirty clauses), and d ⊆ c
            // with |d| >= 2 forces c to contain >= 2 of d's dirty literals.
            if dirty {
                let n = c
                    .lits
                    .iter()
                    .filter(|&&l| {
                        let code = l.code() as usize;
                        code < self.subsume_dirty.len() && self.subsume_dirty[code]
                    })
                    .count();
                if n < 2 {
                    continue;
                }
            }
            sched.push((c.lits.len() as u32, cid));
            has_candidate = true;
        }
        if !has_candidate {
            self.subsume_scratch.schedule = sched;
            self.subsume_scratch.occs = occs;
            self.subsume_scratch.mark = mark;
            return (0, 0);
        }
        if dirty && subsume_round_trace_enabled() {
            let marked: usize = self.subsume_dirty_list.len();
            let space = self.subsume_dirty.len().max(1);
            eprintln!(
                "sub2: scheduled={} marked={}/{} ({:.1}%)",
                sched.len(),
                marked,
                space,
                100.0 * marked as f64 / space as f64
            );
        }
        sched.sort_unstable_by_key(|&(size, _)| size);

        let mut subsumed = 0usize;
        let mut strengthened = 0usize;

        for &(_, cid) in &sched {
            if subchecks >= budget || self.trivially_unsat {
                break;
            }
            let lits: SmallVec<[Lit; 8]> = match self.clauses.get(cid) {
                Some(c) if !c.deleted && c.lits.len() >= 3 => c.lits.iter().copied().collect(),
                _ => continue,
            };

            // Signed-mark the candidate's literals: `l ∈ c` marks +1 on
            // `l.code()` and -1 on `l.negate().code()`, so a connected clause
            // literal `d` reads mark +1 iff `d ∈ c` and -1 iff `¬d ∈ c`.
            for &l in &lits {
                mark[l.code() as usize] = 1;
                mark[l.negate().code() as usize] = -1;
            }

            let mut outcome: Option<SubCheck> = None;

            'candidate: for &l in &lits {
                // cadical: only dirty literals' occurrences can hold new
                // subsumers (all-dirty connected clauses).
                if dirty {
                    let code = l.code() as usize;
                    if !self.subsume_dirty[code] {
                        continue;
                    }
                }
                // Binary fast path.  An edge `¬l → other` in the binary
                // implication graph is the clause `D = (l ∨ other)` (when `¬l`
                // becomes false, `other` is forced true).  Since `l ∈ c` is
                // marked, `D ⊆ c` holds iff `other` is marked +, and `D`
                // self-subsumes `c` iff `¬other` is marked - (resolve `¬other`
                // away).  NOTE the lookup key is `l.negate()`: edges keyed
                // under `l` itself encode `(¬l ∨ other)`, which cannot be a
                // subset of `c` at all – reading them was a false-subsumption
                // bug that deleted live clauses and flipped UNSAT to SAT.
                for &(other, bin_id) in self.binary_graph.get(l.negate()).iter() {
                    // A binary-graph edge may outlive its clause (deletion
                    // paths that don't scrub the graph). Subsuming against a
                    // dead edge deletes live clauses on the word of a clause
                    // the formula no longer contains.
                    if self.clauses.get(bin_id).is_none_or(|c| c.deleted) {
                        continue;
                    }
                    let m = mark[other.code() as usize];
                    if m > 0 {
                        outcome = Some(SubCheck::Subsumed { subsumer: bin_id });
                        break 'candidate;
                    }
                    if m < 0 {
                        // `¬other ∈ c`: remove it.
                        outcome = Some(SubCheck::Strengthen {
                            remove: other.negate(),
                            subsumer: bin_id,
                        });
                        break 'candidate;
                    }
                }

                // Longer connected clauses.
                for &did in occs[l.code() as usize].iter() {
                    let Some(d) = self.clauses.get(did) else {
                        continue;
                    };
                    if d.deleted {
                        continue;
                    }
                    subchecks = subchecks.saturating_add(1);
                    let mut flipped: Option<Lit> = None;
                    let mut failed = false;
                    for &dl in d.lits.iter() {
                        let m = mark[dl.code() as usize];
                        if m == 0 {
                            failed = true;
                            break;
                        }
                        if m > 0 {
                            continue;
                        }
                        // Complemented occurrence: allow exactly one.
                        if flipped.is_some() {
                            failed = true;
                            break;
                        }
                        flipped = Some(dl);
                    }
                    if failed {
                        continue;
                    }
                    match flipped {
                        None => {
                            outcome = Some(SubCheck::Subsumed { subsumer: did });
                            break 'candidate;
                        }
                        // `dl ∉ c` but `¬dl ∈ c`: strengthen by removing
                        // `¬dl` from the candidate.
                        Some(dl) => {
                            outcome = Some(SubCheck::Strengthen {
                                remove: dl.negate(),
                                subsumer: did,
                            });
                            break 'candidate;
                        }
                    }
                }
                if subchecks >= budget {
                    break;
                }
            }

            // Unmark (both polarities).
            for &l in &lits {
                mark[l.code() as usize] = 0;
                mark[l.negate().code() as usize] = 0;
            }

            match outcome {
                Some(SubCheck::Subsumed { subsumer }) => {
                    // cadical `subsume_clause`: deleting an *irredundant*
                    // (original) clause on the word of a *redundant*
                    // (learned) subsumer is only sound if the subsumer
                    // becomes permanent – promote it to irredundant. A
                    // learned subsumer can otherwise die later (database
                    // reduction, elimination of its variables), leaving the
                    // deleted original's obligation uncovered: the final
                    // model then violates an entailed clause and therefore
                    // an original clause (false SAT; reproduced by
                    // `crn_11_99_u`, where learned (57∨1101) subsumed
                    // (37∨57∨1101) and reduction later removed it).
                    let subsumed_learned = self.clauses.get(cid).is_some_and(|c| c.learned)
                        && !crate::nopromote_enabled();
                    if !subsumed_learned && self.clauses.get(subsumer).is_some_and(|s| s.learned) {
                        self.clauses.clear_learned(subsumer);
                    }
                    if let Some(c) = self.clauses.get(cid) {
                        // Re-arm elimination for the variables of the removed
                        // clause (cadical `elim_update_removed_clause`).
                        let lits: SmallVec<[Lit; 8]> = c.lits.iter().copied().collect();
                        self.mark_elim_vars(lits.iter().copied());
                    }
                    // Deletion by the stored LRAT id (id 0 under proofs would
                    // be an invalid line): emit while the clause is still
                    // live so `drat_delete` reads its literals.
                    self.drat_delete(cid);
                    self.retire_clause(cid);
                    self.stats.deleted_clauses += 1;
                    self.stats.subsumed_removed += 1;
                    subsumed += 1;
                    continue;
                }
                Some(SubCheck::Strengthen { remove, subsumer }) => {
                    if let Some(idx) = lits.iter().position(|&l| l == remove) {
                        // Proof emission comes FIRST (it reads the full
                        // pre-shrink clause): the strengthened clause
                        // `kept = c \ {remove}` is the resolvent of `c` with
                        // `subsumer` on `remove`'s variable — under `¬kept`
                        // every `subsumer` literal except the flipped one is
                        // false, the subsumer is unit on it, propagation
                        // makes `remove` false, and `c` conflicts. The
                        // schedule's no-assigned-literal filter guarantees
                        // neither parent carries a level-0 literal, so the
                        // pair needs no unit hints. A parent without a
                        // bound LRAT id skips the strengthen (weaker,
                        // sound); the physical shrink below is then
                        // proof-silent for this path.
                        let emitted = if self.proof.is_some() {
                            self.proof_strengthen_clause_res(cid, subsumer, &lits, idx)
                        } else {
                            true
                        };
                        if emitted {
                            // Re-arm elimination for the shrunken clause's
                            // variables (cadical marks on `shrink_clause`).
                            self.mark_elim_vars(lits.iter().copied());
                            self.strengthen_clause_in_subsume(cid, idx);
                            strengthened += 1;
                        }
                    }
                    // Fall through: also connect the (possibly strengthened) clause.
                }
                None => {}
            }

            // Connect the clause on its least-occurring literal so later,
            // larger candidates can match against it (cadical one-watch).
            let cur: SmallVec<[Lit; 8]> = match self.clauses.get(cid) {
                Some(c) if !c.deleted => c.lits.iter().copied().collect(),
                _ => continue,
            };
            let mut minlit = cur[0];
            let mut minsize = occs[minlit.code() as usize].len();
            for &l in &cur[1..] {
                let size = occs[l.code() as usize].len();
                if size < minsize {
                    minlit = l;
                    minsize = size;
                }
            }
            // cadical: connect only clauses whose EVERY literal is dirty —
            // a clean literal means candidates never scan the list this
            // clause would join, so connecting it is pure waste.
            // HOT-LITERAL PROBABILISTIC CONNECT (`NIXIE_SUBSUME2_HOTP`): a
            // not-all-dirty clause still connects with probability p, but
            // on the least-occurring AMONG ITS DIRTY literals — random
            // clean-literal placement would be invisible to candidates
            // (they scan only dirty literals); a dirty-literal watch is
            // discoverable by exactly the candidates plausibly containing
            // this clause.  Deterministic draw (clause-id hash).
            let hotp = subsume2_hotp();
            let all_dirty = !dirty || cur.iter().all(|&l| self.subsume_dirty[l.code() as usize]);
            let mut connect_lit = minlit;
            let mut do_connect = all_dirty;
            if !all_dirty && hotp > 0 {
                let mut hot: Option<Lit> = None;
                let mut hot_size = usize::MAX;
                for &l in cur.iter() {
                    if self.subsume_dirty[l.code() as usize] {
                        let size = occs[l.code() as usize].len();
                        if size < hot_size {
                            hot = Some(l);
                            hot_size = size;
                        }
                    }
                }
                if let Some(h) = hot {
                    let draw = (cid.index().wrapping_mul(0x9E37_79B9).wrapping_add(
                        (self.subsume_rounds_done as usize).wrapping_mul(0x85EB_CA6B),
                    )) % 1000;
                    if draw < hotp as usize {
                        connect_lit = h;
                        do_connect = true;
                        minsize = hot_size;
                    }
                }
            }
            // Do not connect a clause through an over-long list.
            if minsize <= 100 && do_connect {
                occs[connect_lit.code() as usize].push(cid);
            }
        }

        if dirty {
            // Round end (cadical): clear the dirty set.  The randomized
            // mode (default) instead re-places the same count of codes
            // uniformly (deterministic xorshift) — the measured winner.
            let null_arm = subsume2_null() || subsume2_mode() == SubsumeScheduleMode::RandomSlice;
            for &code in &self.subsume_dirty_list {
                let c = code as usize;
                if c < self.subsume_dirty.len() {
                    self.subsume_dirty[c] = false;
                }
            }
            let n_marked = self.subsume_dirty_list.len();
            self.subsume_dirty_list.clear();
            if null_arm && n_marked > 0 {
                let mut x: u64 = 0x9E37_79B9_7F4A_7C15_u64
                    .wrapping_add(n_marked as u64)
                    .wrapping_mul(0xBF58_476D_1CE4_E5B9);
                let space = self.subsume_dirty.len() as u64;
                for _ in 0..n_marked {
                    x ^= x << 13;
                    x ^= x >> 7;
                    x ^= x << 17;
                    let code = (x % space) as usize;
                    if !self.subsume_dirty[code] {
                        self.subsume_dirty[code] = true;
                        self.subsume_dirty_list.push(code as u32);
                    }
                }
            }
        }

        (subsumed, strengthened)
    }

    /// Strengthen `clause_id` by dropping the literal at `idx`, keeping
    /// watches/BIG, and proof stream consistent.
    ///
    /// A result of length 2 is entered into the binary implication graph by
    /// the `attach_watchers` call inside `remove_literal_and_rewatch`
    /// (BIG-authoritative BCP, 2026-09), so binary propagation keeps seeing
    /// it.
    fn strengthen_clause_in_subsume(&mut self, clause_id: ClauseId, idx: usize) {
        let learned = self.clauses.get(clause_id).is_some_and(|c| c.learned);
        // Proof-silent: the caller emitted the resolution-justified event
        // (`proof_strengthen_clause_res`) before the physical shrink.
        self.remove_literal_and_rewatch_silent(clause_id, idx);
        if learned
            && let Some(c) = self.clauses.get(clause_id)
            && !c.deleted
        {
            // cadical `shrink_clause`: a shrunken redundant clause's glue is
            // clamped to `min(size - 1, glue)` (glue only ever decreases).
            // Without the clamp a learned clause's stale LBD can exceed its
            // new length, tripping the LBD≤length invariant at the next
            // consistency check.
            let cap = (c.lits.len().saturating_sub(1).max(1)) as u32;
            if c.lbd > cap {
                self.clauses.set_lbd(clause_id, cap);
            }
        }
        // A result of length 2 needs no extra registration here: the
        // `attach_watchers` call inside `remove_literal_and_rewatch`
        // above enters new binaries into the BIG (BIG-authoritative BCP,
        // 2026-09) – adding edges here again would duplicate them and
        // double the phantom tick count.
    }
}
