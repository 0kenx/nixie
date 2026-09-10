//! Global forward subsumption with strengthening (port of CaDiCaL `subsume.cpp`).
//!
//! For every scheduled clause `c` (ascending size) we look for an already
//! *connected* clause `d` (smaller or equal size) whose literals all occur in
//! `c` – then `c` is subsumed and deleted – or that occur in `c` except for
//! exactly one complementary literal – then that literal is removed from `c`
//! (self-subsuming resolution). A surviving clause, including after
//! strengthening, is *connected* into the one-watched
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
    pub(super) occs: Vec<SmallVec<[Connection; 4]>>,
    pub(super) mark: Vec<i8>,
    payloads: ConnectedPayloads,
}

/// Offset into this round's immutable payload store. Only `connect` creates
/// production offsets. The database oracle interprets its own entries as IDs.
#[derive(Clone, Copy, Debug)]
pub(super) struct Connection(u32);

/// Clauses already processed by the forward schedule cannot be strengthened
/// or retired again during this round. Later candidates can only promote a
/// connected subsumer's metadata. Copy its post-strengthening literals once,
/// retaining the stable database ID for promotion and current proof-ID lookup.
///
/// The connection literal is omitted: the occurrence-list key supplies its
/// signed mark once per candidate bucket. Records are
/// `[residual_length, database_id, residual_literal_codes...]`. All accesses use
/// checked slices; no arena pointer, stale proof ID or unsafe cast is stored.
#[derive(Default, Clone, Debug)]
struct ConnectedPayloads {
    words: Vec<u32>,
}

impl ConnectedPayloads {
    fn connect(&mut self, id: ClauseId, lits: &[Lit], key: Lit) -> Connection {
        let omitted = lits
            .iter()
            .position(|lit| *lit == key)
            .unwrap_or_else(|| panic!("subsumption connection literal is absent"));
        let offset = u32::try_from(self.words.len())
            .unwrap_or_else(|_| panic!("subsumption payload address space exhausted"));
        let len = u32::try_from(lits.len() - 1)
            .unwrap_or_else(|_| panic!("subsumption payload length overflow"));
        self.words.reserve(
            lits.len()
                .checked_add(1)
                .unwrap_or_else(|| panic!("subsumption payload capacity overflow")),
        );
        self.words.push(len);
        self.words.push(id.0);
        self.words
            .extend(lits[..omitted].iter().map(|lit| lit.code()));
        self.words
            .extend(lits[omitted + 1..].iter().map(|lit| lit.code()));
        Connection(offset)
    }

    #[inline]
    fn get(&self, connection: Connection) -> (ClauseId, &[u32]) {
        let (header, tail) = self.words[connection.0 as usize..].split_at(2);
        (ClauseId::new(header[1]), &tail[..header[0] as usize])
    }
}

/// The signed-mark test is shared with the database-backed test oracle.
/// Residual order is preserved. Successful SSR selects the same unique
/// complemented literal; rejected checks may stop earlier after key seeding.
#[inline]
fn check_connected(
    lits: impl Iterator<Item = Lit>,
    mark: &[i8],
    mut flipped: Option<Lit>,
) -> ConnectedCheck {
    for lit in lits {
        let m = mark[lit.code() as usize];
        if m == 0 {
            return ConnectedCheck::Mismatch;
        }
        if m > 0 {
            continue;
        }
        if flipped.is_some() {
            return ConnectedCheck::Mismatch;
        }
        flipped = Some(lit);
    }
    match flipped {
        None => ConnectedCheck::Subsumed,
        Some(lit) => ConnectedCheck::Strengthen(lit.negate()),
    }
}

#[derive(Debug, PartialEq, Eq)]
enum ConnectedCheck {
    Mismatch,
    Subsumed,
    Strengthen(Lit),
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
    /// Z3-style backward self-subsuming resolution before search.
    ///
    /// CaDiCaL one-watch subsumption never connects these clauses: a 4-in-4-out
    /// LUT cube has occurrence ≥240 > `subsumeocclim` (100), so the 168k
    /// width-8 cubes on `circuit_48in64out` never become subsumers. Z3's first
    /// simplify instead walks every occurrence of the minimum-occurrence
    /// variable (both polarities) and shrinks 168k cubes to ~69k mixed-width
    /// clauses. This pass is that slice — original clauses only, level 0.
    ///
    /// Auto-runs on wide-uniform CNFs (modal original width ≥6 covering ≥75%
    /// of size≥3 originals, ≥1000 such clauses). One backward round by default
    /// (`NIXIE_PRESUB_ROUNDS`); extra rounds reshuffle this family. `NIXIE_PRESUB=1`
    /// forces it; `NIXIE_PRESUB=0` skips it.
    pub(super) fn presearch_backward_simplify(&mut self) -> bool {
        if self.trail.decision_level() != 0 || self.trivially_unsat {
            return false;
        }
        if !self.presearch_backward_simplify_wanted() {
            return false;
        }
        let max_rounds = {
            #[cfg(feature = "std")]
            {
                std::env::var("NIXIE_PRESUB_ROUNDS")
                    .ok()
                    .and_then(|v| v.parse().ok())
                    .filter(|n: &u32| *n >= 1)
                    .unwrap_or(1)
            }
            #[cfg(not(feature = "std"))]
            {
                1u32
            }
        };
        for round in 0..max_rounds {
            let (sub, stren) = self.backward_subsume_round();
            #[cfg(feature = "std")]
            if std::env::var("NIXIE_PRESUB_TRACE").is_ok() {
                eprintln!(
                    "c [presub] round={} subsumed={} strengthened={} orig={}",
                    round,
                    sub,
                    stren,
                    self.clauses.num_original()
                );
            }
            if sub == 0 && stren == 0 {
                break;
            }
            self.rebuild_watches_and_binary_graph();
            if let Some(conflict) = self.propagate() {
                self.trivially_unsat = true;
                self.drat_emit_empty(Some(conflict));
                return true;
            }
        }
        if self.config.enable_failed_literal_probing {
            let failed = {
                #[cfg(feature = "std")]
                let z3probe = std::env::var("NIXIE_PRESUB_Z3PROBE")
                    .is_ok_and(|v| v == "1" || v.eq_ignore_ascii_case("true"));
                #[cfg(not(feature = "std"))]
                let z3probe = false;
                if z3probe {
                    self.probe_both_polarities()
                } else {
                    let (_probed, failed, _hyper) = self.probe_round();
                    failed
                }
            };
            #[cfg(feature = "std")]
            if std::env::var("NIXIE_PRESUB_TRACE").is_ok() {
                eprintln!(
                    "c [presub] probe_failed={failed} trail={}",
                    self.trail.size()
                );
            }
            if self.trivially_unsat {
                return true;
            }
            if failed > 0 {
                self.rebuild_watches_and_binary_graph();
                if let Some(conflict) = self.propagate() {
                    self.trivially_unsat = true;
                    self.drat_emit_empty(Some(conflict));
                    return true;
                }
            }
        }
        #[cfg(feature = "std")]
        if let Ok(path) = std::env::var("NIXIE_DUMP_POSTSSR") {
            self.debug_dump_cnf(&path);
        }
        false
    }

    fn presearch_backward_simplify_wanted(&self) -> bool {
        #[cfg(feature = "std")]
        {
            if let Ok(v) = std::env::var("NIXIE_PRESUB") {
                if v == "0" || v.eq_ignore_ascii_case("false") {
                    return false;
                }
                if v == "1" || v.eq_ignore_ascii_case("true") {
                    return true;
                }
            }
        }
        self.formula_is_wide_uniform_cnf()
    }

    fn formula_is_wide_uniform_cnf(&self) -> bool {
        let mut hist = [0u32; 33];
        let mut n = 0u32;
        for cid in self.clauses.iter_ids() {
            let Some(c) = self.clauses.get(cid) else {
                continue;
            };
            if c.deleted || c.learned {
                continue;
            }
            let size = c.lits.len();
            if size < 3 {
                continue;
            }
            n = n.saturating_add(1);
            if size < hist.len() {
                hist[size] = hist[size].saturating_add(1);
            }
        }
        if n < 1000 {
            return false;
        }
        let mut mode = 0usize;
        let mut best = 0u32;
        for (size, &cnt) in hist.iter().enumerate() {
            if cnt > best {
                best = cnt;
                mode = size;
            }
        }
        mode >= 6 && u64::from(best).saturating_mul(4) >= u64::from(n).saturating_mul(3)
    }

    /// One backward-subsumption / SSR round (Z3 `back_subsumption1` over all
    /// original clauses, small-first). Returns `(subsumed, strengthened)`.
    pub(super) fn backward_subsume_round(&mut self) -> (usize, usize) {
        if self.trail.decision_level() != 0 || self.trivially_unsat {
            return (0, 0);
        }
        let num_lits = 2 * self.num_vars;
        if num_lits == 0 {
            return (0, 0);
        }
        let mut occs: Vec<Vec<ClauseId>> = vec![Vec::new(); num_lits];
        let mut sched: Vec<(u32, ClauseId)> = Vec::new();
        for cid in self.clauses.iter_ids() {
            let Some(c) = self.clauses.get(cid) else {
                continue;
            };
            if c.deleted || c.learned || c.lits.len() < 2 {
                continue;
            }
            if c.lits.iter().any(|&l| self.trail.lit_val(l) != 0) {
                continue;
            }
            for &l in c.lits.iter() {
                let code = l.code() as usize;
                if code < occs.len() {
                    occs[code].push(cid);
                }
            }
            sched.push((c.lits.len() as u32, cid));
        }
        if sched.is_empty() {
            return (0, 0);
        }
        sched.sort_unstable_by_key(|&(size, _)| size);

        let mut mark = vec![0i8; num_lits];
        let mut subsumed = 0usize;
        let mut strengthened = 0usize;
        let mut checks: u64 = 0;
        const CHECK_CAP: u64 = 100_000_000;

        for &(_, c1_id) in &sched {
            if checks >= CHECK_CAP || self.trivially_unsat {
                break;
            }
            let c1_lits: SmallVec<[Lit; 8]> = match self.clauses.get(c1_id) {
                Some(c) if !c.deleted && c.lits.len() >= 2 => c.lits.iter().copied().collect(),
                _ => continue,
            };
            let mut minlit = c1_lits[0];
            let mut minocc = occs[minlit.code() as usize].len();
            for &l in &c1_lits[1..] {
                let occ = occs[l.code() as usize].len();
                if occ < minocc {
                    minlit = l;
                    minocc = occ;
                }
            }
            let pos_list = minlit.code() as usize;
            let neg_list = minlit.negate().code() as usize;
            for list in [pos_list, neg_list] {
                if list >= occs.len() {
                    continue;
                }
                let candidates = occs[list].clone();
                for c2_id in candidates {
                    if checks >= CHECK_CAP {
                        break;
                    }
                    if c2_id == c1_id {
                        continue;
                    }
                    let c2_lits: SmallVec<[Lit; 8]> = match self.clauses.get(c2_id) {
                        Some(c) if !c.deleted && !c.learned && c.lits.len() >= 2 => {
                            c.lits.iter().copied().collect()
                        }
                        _ => continue,
                    };
                    if c2_lits.len() + 1 < c1_lits.len() {
                        continue;
                    }
                    checks = checks.saturating_add(1);
                    for &l in &c2_lits {
                        let code = l.code() as usize;
                        if code < mark.len() {
                            mark[code] = 1;
                            mark[l.negate().code() as usize] = -1;
                        }
                    }
                    let check = check_connected(c1_lits.iter().copied(), &mark, None);
                    for &l in &c2_lits {
                        let code = l.code() as usize;
                        if code < mark.len() {
                            mark[code] = 0;
                            mark[l.negate().code() as usize] = 0;
                        }
                    }
                    match check {
                        ConnectedCheck::Mismatch => {}
                        ConnectedCheck::Subsumed => {
                            self.drat_delete(c2_id);
                            self.retire_clause(c2_id);
                            self.stats.deleted_clauses += 1;
                            self.stats.subsumed_removed += 1;
                            subsumed += 1;
                        }
                        ConnectedCheck::Strengthen(remove) => {
                            if let Some(idx) = c2_lits.iter().position(|&l| l == remove) {
                                let emitted = if self.proof.is_some() {
                                    self.proof_strengthen_clause_res(c2_id, c1_id, &c2_lits, idx)
                                } else {
                                    true
                                };
                                if emitted {
                                    self.mark_elim_vars(c2_lits.iter().copied());
                                    self.strengthen_clause_in_subsume(c2_id, idx);
                                    self.stats.self_subsumed += 1;
                                    strengthened += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
        (subsumed, strengthened)
    }

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
        #[cfg(test)]
        if self.subsume_database_oracle {
            return self.subsume_round_impl::<false>();
        }
        self.subsume_round_impl::<true>()
    }

    fn subsume_round_impl<const CACHED: bool>(&mut self) -> (usize, usize) {
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
        let mut payloads = std::mem::take(&mut self.subsume_scratch.payloads);
        // No connection is evidence across rounds, scopes or arena collection.
        payloads.words.clear();
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
            debug_assert!(occs.iter().all(|entry| entry.is_empty()));
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
            self.subsume_scratch.payloads = payloads;
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

                // A scheduled ID is processed once, then connected. The only
                // clause mutated below is the current candidate; promotion of
                // a previous subsumer does not change its copied literals.
                let key_mark = mark[l.code() as usize];
                let key_flipped = (key_mark < 0).then_some(l);
                for &connection in occs[l.code() as usize].iter() {
                    let (did, check) = if CACHED {
                        let (did, codes) = payloads.get(connection);
                        #[cfg(debug_assertions)]
                        {
                            let d = self
                                .clauses
                                .get(did)
                                .unwrap_or_else(|| panic!("connected subsumer disappeared"));
                            assert!(!d.deleted, "connected subsumer was retired");
                            let omitted = d
                                .lits
                                .iter()
                                .position(|lit| *lit == l)
                                .unwrap_or_else(|| panic!("connected key disappeared"));
                            assert!(
                                d.lits[..omitted]
                                    .iter()
                                    .chain(&d.lits[omitted + 1..])
                                    .map(|lit| lit.code())
                                    .eq(codes.iter().copied()),
                                "connected subsumer changed after being processed"
                            );
                        }
                        subchecks = subchecks.saturating_add(1);
                        (
                            did,
                            if key_mark == 0 {
                                ConnectedCheck::Mismatch
                            } else {
                                check_connected(
                                    codes.iter().copied().map(Lit::from_code),
                                    &mark,
                                    key_flipped,
                                )
                            },
                        )
                    } else {
                        let did = ClauseId::new(connection.0);
                        let Some(d) = self.clauses.get(did) else {
                            continue;
                        };
                        if d.deleted {
                            continue;
                        }
                        subchecks = subchecks.saturating_add(1);
                        (did, check_connected(d.lits.iter().copied(), &mark, None))
                    };
                    match check {
                        ConnectedCheck::Mismatch => continue,
                        ConnectedCheck::Subsumed => {
                            outcome = Some(SubCheck::Subsumed { subsumer: did });
                            break 'candidate;
                        }
                        ConnectedCheck::Strengthen(remove) => {
                            outcome = Some(SubCheck::Strengthen {
                                remove,
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
                // Copy only after strengthening, proof handling and watch
                // reordering, and only if the existing policy connects it.
                let connection = if CACHED {
                    payloads.connect(cid, &cur, connect_lit)
                } else {
                    Connection(cid.0)
                };
                occs[connect_lit.code() as usize].push(connection);
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

        if CACHED {
            // The old normal exit dropped these buffers. Retain capacity for
            // both the occurrence lists and their new compact payloads. Every
            // candidate is unmarked before any normal or budget exit.
            // Only empty buffers escape the round. This also prevents idle
            // connections from surviving a scope change or collection.
            sched.clear();
            for entry in &mut occs {
                entry.clear();
            }
            payloads.words.clear();
            self.subsume_scratch.schedule = sched;
            self.subsume_scratch.occs = occs;
            self.subsume_scratch.mark = mark;
            self.subsume_scratch.payloads = payloads;
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

#[cfg(test)]
#[path = "subsume_payload_tests.rs"]
mod payload_tests;
