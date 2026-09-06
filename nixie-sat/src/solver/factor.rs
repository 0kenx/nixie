//! Full port of kissat's `factor.c` — quotient-chain bounded variable
//! addition (the worker-class lever).
//!
//! # The mechanism (kissat `factor.c`, all defaults on: `factor=1`,
//! `factorsize=5`, `factorcandrounds=2`, `factordelay=4`, `factoriniticks=700`,
//! `factoreffort=50‰`, `factorstructural=0`)
//!
//! A **quotient chain** `q_0 → q_1 → … → q_b` is grown one pivot at a time.
//! `q_0.factor = x_1` with `q_0.clauses` = every live clause containing `x_1`
//! (binaries from the BIG's adjacency — original *and* learned, as in
//! kissat's binary watches; large original clauses of size `3..=FACTOR_SIZE`
//! whose *every* literal has binary+large occurrence `≥ 2` — kissat's
//! `connect_clauses_to_factor` candidate filter, here an explicit
//! occurrence index).  Each extension picks the next pivot `x_{k+1}` by
//! counting, over the chain tail's clauses `(x_k ∨ A_j)`, the literals `x`
//! that co-occur in a **matching** clause — binary `(q ∨ x)` for a binary
//! tail clause `(x_k ∨ q)`, or a same-size large clause `d` whose literals
//! are exactly the tail clause's non-pivot literals plus `x`.  Only the
//! *matched* clauses survive into the new link (`matches[i]` indexes the
//! previous link's list), so the pattern sets `A_j` shrink organically —
//! kissat's incremental chain, not a bulk co-occurrence intersection (the
//! measured-negative shapes listed in `docs/handovers/`).
//!
//! `best_quotient` then evaluates every prefix cut `p`: with `n = |q_p|`
//! matched patterns and `p+1` factors, the rewrite deletes `(p+1)·n` clauses
//! `(x_i ∨ A_j)` and adds `p+1` dividers `(t ∨ x_i)` plus `n` quotients
//! `(¬t ∨ A_j)` — reduction `n·(p+1) − n − (p+1)`.  Applied when the best
//! reduction exceeds the bound (kissat's escalating `eliminate` bound starts
//! at 0; we keep 0 — divergence recorded below).
//!
//! # Soundness
//!
//! For the applied cut the deleted set is exactly
//! `S = { (x_i ∨ A_j) : i ≤ p, j < n }` and the added set is
//! `S' = { (t ∨ x_i) } ∪ { (¬t ∨ A_j) }`:
//!
//! * **old → new**: a model of `S` with every `A_j` satisfiable picks
//!   `t := true` (dividers hold; quotients hold through `A_j`); a model with
//!   some `A_j` fully false has every `x_i` true (each `(x_i ∨ A_j)` forces
//!   it), so `t := false` satisfies the quotients and every divider.
//! * **new → old**: `t` true forces every `A_j`; `t` false forces every
//!   `x_i` — either way each `(x_i ∨ A_j)` is satisfied by the model's
//!   restriction to the original variables.  (Equivalently: the added
//!   clauses say `¬x_i → t → A_j`, the deleted ones `¬A_j → x_i` —
//!   contrapositives of each other.)
//!
//! The transformation is equisatisfiable **and** model-preserving downward,
//! so no reconstruction record is needed.  Learned *binaries* may
//! participate (kissat factors every binary watch): replacing a set of
//! clauses by an equisatisfiable-in-context set preserves the full-database
//! satisfiability class in both directions, learned or not.  Large
//! candidates stay original-only, as in kissat.
//!
//! # Variable schedule — the handover doc's reading is inverted
//!
//! `docs/handovers/2026-09-07-factor-port.md` says kissat "pushes the fresh
//! hub to the FRONT of the VMTF queue, making it the next decision".  The
//! source says the opposite: `adjust_scores_and_phases_of_fresh_variables`
//! dequeues each fresh variable, relinks it at `queue->first` — the
//! **oldest** end, reached last by `kissat_decide`'s scan from
//! `queue->last` — sets its VSIDS score to **0**, and restamps the list so
//! fresh variables carry the smallest stamps.  Fresh hubs are decided
//! **last**, not first (in focused VMTF *and* stable VSIDS mode alike).
//! This port follows the source (`NIXIE_FACTOR_SCHED=back`, the default);
//! `=front` (bump-to-tail: next decision — the handover's claim) and
//! `=leave` (our `new_var` default, which enqueues at the tail) are retained
//! as measured arms.  Our `new_var` already inserts at activity 0, so the
//! VSIDS half of the adjustment is a no-op here.
//!
//! # Delivery and budget (kissat semantics)
//!
//! * **Dirty-literal gating** (`flags.factor` bits, set wherever kissat's
//!   `kissat_mark_added_literal` runs — our `mark_subsume_lit` sites): the
//!   candidate heap only ever processes literals whose clause set changed
//!   since they were last factored; a completed pass sets the watermark and
//!   later passes are skipped until new marks arrive.
//! * **Ticks** (cache-line-estimated scan work, cumulative in
//!   `stats.factor_ticks`): first pass bounded by `FACTOR_INIT_TICKS`
//!   (kissat `factoriniticks=700` M), later passes by
//!   `50‰ × max(window, 10M)` of search work since the last round (kissat
//!   `factoreffort=50`, `mineffort=10`).
//! * **Delay** (kissat `factordelay=4`): skip while
//!   `log10(active vars) > rounds + 4` — worker-class instances (93k vars ⇒
//!   log10 ≈ 4.97) factor from the first round on, exactly as in kissat.
//! * **Incremental delivery**: introductions happen one chain at a time
//!   inside the pass, with dividers/quotients connected to the BIG and the
//!   occurrence index immediately (kissat connects them in dense mode), so
//!   later chains in the same pass match the new structure — the fixpoint
//!   the measured-negative "mega-round" delivery lacked.
//!
//! # Divergences from `factor.c` (recorded)
//!
//! * `factorstructural`/`factorhops` (tie-break scores by multi-hop path
//!   counting) are **off by default in kissat** and not ported; ties break
//!   by watch size (`watches_score`) with first-seen-wins, as the default
//!   configuration does.
//! * The elimination-bound escalation (`bound` 0→16) is not ported (our
//!   inprocessing has no equivalent escalating bound); the bound stays 0.
//! * Eager O(1) watch-list removal (`eagerly_remove_watch`) is replaced by
//!   tombstone retirement (`ClauseDatabase::remove`, O(1) probe via the
//!   pass's `dead` bitset) plus **periodic BIG compaction**
//!   ([`Solver::factor_maybe_compact`]) — a batched analogue that keeps
//!   scans tight without per-deletion memmoves.  Between compactions the
//!   candidate-heap scores are snapshots (raw list lengths) — they only
//!   steer pop order, never correctness (every match re-validates
//!   liveness).
//! * `update_factored` parity: the fresh hub `t` is never pushed into the
//!   schedule (kissat's `update_factored` touches only the chain factors
//!   and chain clauses) — pushing it lets the pass factor hub clauses
//!   against each other, building mega-clusters whose conflict clauses
//!   span thousands of decision levels (measured avg_lbd ≈ 1100 on
//!   worker_550 before the exclusion; kissat sits at ≈ 227
//!   decisions/conflict).
//! * The next-pivot boundary check excludes code `== initial` as well as
//!   `> initial` (kissat's `next > initial` admits exactly the first fresh
//!   literal; our arrays are sized `initial`, so the boundary code is
//!   excluded — a one-literal divergence per pass).
//! * kissat's per-watch `factor_ticks` are mirrored as `1 + len/8` per
//!   scanned list plus 1 per clause visit/add/delete.
//! * `TERMINATED(factor_terminated_1)` (external termination) is not ported;
//!   the tick budget bounds the pass.
//! * The occurrence-index fixed point runs exactly `factorcandrounds`
//!   reduction rounds without kissat's early stop when candidates stop
//!   shrinking (the fixed point is reached either way; the connected set
//!   can differ only in non-shrinking iterations).
//!
//! Gates (as every rewriting pass here): decision level 0, base assertion
//! scope only, no attached proof/LRAT tracer, no real theory.  Default off
//! (`SolverConfig::enable_factoring` or `NIXIE_FACTOR=1`).

use crate::clause::ClauseId;
use crate::literal::{Lit, Var};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;

use super::Solver;

/// kissat `factorsize` (5): maximum clause length participating in chains.
const FACTOR_SIZE: usize = 5;
/// kissat `factorcandrounds` (2): occurrence-filter fixed-point rounds.
const FACTOR_CAND_ROUNDS: u32 = 2;
/// kissat `factordelay` (4): skip while `log10(active) > rounds + delay`.
const FACTOR_DELAY: u64 = 4;
/// kissat `factoriniticks` (700, in millions): first-pass tick budget.
const FACTOR_INIT_TICKS: u64 = 700_000_000;
/// kissat `factoreffort` (50‰) and `mineffort` (10 → 10M reference floor).
const FACTOR_EFFORT_PERMILLE: u64 = 50;
const FACTOR_MIN_REFERENCE: u64 = 10_000_000;
/// BIG compaction trigger: tombstones since the last sweep.
const FACTOR_COMPACT_THRESHOLD: usize = 1_000_000;

/// Mark bits over literal codes (kissat `FACTOR`/`QUOTIENT`/`NOUNTED`).
const MARK_FACTOR: u8 = 1;
const MARK_QUOTIENT: u8 = 2;
const MARK_NOUNTED: u8 = 4;

/// Env override for the tick budget (diagnostics; applies to every pass).
fn factor_budget_override() -> Option<u64> {
    #[cfg(feature = "std")]
    {
        std::env::var("NIXIE_FACTOR_BUDGET")
            .ok()
            .and_then(|v| v.parse().ok())
    }
    #[cfg(not(feature = "std"))]
    {
        None
    }
}

/// Whether the chain factor is enabled (config flag or `NIXIE_FACTOR=1`).
pub(super) fn factor_enabled_cfg(config: &super::SolverConfig) -> bool {
    if config.enable_factoring {
        return true;
    }
    #[cfg(feature = "std")]
    {
        std::env::var("NIXIE_FACTOR").as_deref() == Ok("1")
    }
    #[cfg(not(feature = "std"))]
    {
        false
    }
}

/// Fresh-variable schedule arm (see [`Solver::factor_adjust_fresh`]).
enum FactorSched {
    /// kissat default: oldest end of VMTF (decided last); VSIDS score 0.
    Back,
    /// The handover doc's reading: bump to the tail (next decisions).
    Front,
    /// No adjustment (our `new_var` already enqueues at the tail).
    Leave,
}

fn factor_sched_mode() -> FactorSched {
    #[cfg(feature = "std")]
    {
        match std::env::var("NIXIE_FACTOR_SCHED").as_deref() {
            Ok("front") => FactorSched::Front,
            Ok("leave") => FactorSched::Leave,
            _ => FactorSched::Back,
        }
    }
    #[cfg(not(feature = "std"))]
    {
        FactorSched::Back
    }
}

/// Whether per-chain shape tracing is on (`NIXIE_FACTOR_TRACE=2`, first 20
/// chains).
fn chain_trace_enabled(applies: usize) -> bool {
    #[cfg(feature = "std")]
    {
        std::env::var("NIXIE_FACTOR_TRACE").as_deref() == Ok("2") && applies < 20
    }
    #[cfg(not(feature = "std"))]
    {
        let _ = applies;
        false
    }
}

/// One chain link's clause: binary `(factor ∨ q)` or large `(factor ∨ A)`.
///
/// `cid` always names the clause that contains **this link's** factor — the
/// original clause for link 0, the match witness for deeper links (kissat
/// stores the raw watch and re-derives the pair at delete time; we keep the
/// id, which `ClauseDatabase::remove` retires directly).
#[derive(Debug, Clone, Copy)]
struct FEntry {
    /// Binary partner `q` (the pattern's identity) when binary.
    q: Option<Lit>,
    /// The clause containing this link's factor (binary or large).
    cid: ClauseId,
}

/// One link of the quotient chain (kissat `struct quotient`).
#[derive(Debug, Default)]
struct Quotient {
    /// The pivot literal `x_{k+1}`.
    factor: Option<Lit>,
    /// Matched clauses of this link (binary entries carry `q = A_j`).
    clauses: Vec<FEntry>,
    /// `matches[i]`: index into the PREVIOUS link's `clauses` (empty for
    /// link 0).
    matches: Vec<u32>,
}

/// Occurrence index over candidate large clauses (kissat's dense-mode
/// `connect_clauses_to_factor` product): CSR primary by literal code plus a
/// lazily-allocated overflow for the pass's own additions.
#[derive(Debug, Default)]
struct OccIndex {
    /// Exclusive end of each code's primary span.
    span_end: Vec<u32>,
    /// Clause ids, ascending within each span.
    flat: Vec<ClauseId>,
    /// Mid-pass additions (kissat connects added quotients immediately;
    /// keys beyond `initial` are skipped — they can never be pivots).
    extra: FxHashMap<u32, Vec<ClauseId>>,
}

impl OccIndex {
    /// Primary span length of `code` (0 beyond the table — mid-pass fresh
    /// literals have no primary span).
    #[inline]
    fn len(&self, code: u32) -> usize {
        let c = code as usize;
        let Some(&end) = self.span_end.get(c) else {
            return 0;
        };
        let start = if c == 0 {
            0
        } else {
            self.span_end[c - 1] as usize
        };
        (end as usize).saturating_sub(start)
    }

    /// Overflow entry count of `code` (0 beyond the table).
    #[inline]
    fn extra_len(&self, code: u32) -> usize {
        self.extra.get(&code).map_or(0, Vec::len)
    }

    /// Append a mid-pass addition under `code`.
    fn push(&mut self, code: u32, cid: ClauseId) {
        self.extra.entry(code).or_default().push(cid);
    }

    /// Visit every occurrence of `code` (primary then overflow; nothing
    /// beyond the table).
    fn for_each(&self, code: u32, f: &mut impl FnMut(ClauseId)) {
        let c = code as usize;
        let Some(&end) = self.span_end.get(c) else {
            return;
        };
        let start = if c == 0 {
            0
        } else {
            self.span_end[c - 1] as usize
        };
        for &cid in &self.flat[start..end as usize] {
            f(cid);
        }
        if let Some(v) = self.extra.get(&code) {
            for &cid in v {
                f(cid);
            }
        }
    }
}

/// Pass-local state (kissat `struct factoring`).
struct FactorState {
    quotients: Vec<Quotient>,
    /// Per-literal-code marks.  Sized `initial` at pass start and grown with
    /// the literal space (mid-pass-added chain clauses contain fresh
    /// literals and are scanned in later iterations — the pass's own
    /// fixpoint delivery; kissat's solver-wide `marks` array grows with new
    /// variables the same way).
    marks: Vec<u8>,
    /// Per-literal-code candidate counts (kissat `count`).
    count: Vec<u32>,
    /// Codes with `count > 0` (kissat `counted`).
    counted: Vec<u32>,
    /// NOUNTED-marked codes of the current large-clause scan (kissat
    /// `nounted`).
    nounted: Vec<u32>,
    /// Clause-dedup bits (kissat's clause `quotient` header flag), indexed
    /// by clause id (dense `num_slots` id space, grown with the id space).
    qmark: Vec<bool>,
    /// Clause-id indexes marked this scan (kissat `qlauses`), cleared after
    /// each `next_factor`/`factorize_next` call.
    qlauses: Vec<usize>,
    /// Clause tombstones: `dead[cid]` ⇒ retired this pass (our batched
    /// analogue of kissat's eager watch removal; see
    /// [`Solver::factor_maybe_compact`]).  Ids beyond the pass's start
    /// snapshot are freshly added, hence live.
    dead: Vec<bool>,
    /// Tombstones since the last BIG compaction (the trigger).
    dead_since_compact: usize,
    /// Candidate heap: `(raw watch size, literal code)`, lazy (stale entries
    /// are skipped at pop via the dirty bit / activity checks).
    schedule: std::collections::BinaryHeap<(u64, u32)>,
    /// Literal-code space at pass start (kissat `initial = LITS`).
    initial: u32,
    /// Fresh hub variables introduced this pass.
    fresh: Vec<Var>,
    /// Minimum reduction for an application (kissat `bound`; fixed 0 here).
    bound: i64,
    /// Absolute cumulative tick limit for the pass.
    limit: u64,
    /// Ticks spent this pass (flushed into `stats.factor_ticks` at the end).
    ticks: u64,
    /// Introductions this pass.
    introduced: usize,
    /// Shape counters (diagnostics): schedule pops, dirty-processed pops,
    /// chain-extension links, applied chains, and the summed factors (m) and
    /// patterns (n) over applied chains.
    pops: usize,
    processed: usize,
    links: usize,
    applies: usize,
    sum_m: usize,
    sum_n: usize,
}

impl FactorState {
    /// +1 tick; returns whether the cumulative budget is exhausted.
    #[inline]
    fn tick(&mut self) -> bool {
        self.ticks += 1;
        self.ticks >= self.limit
    }

    /// `1 + len/8` — kissat's per-watched-list cache-line estimate.
    #[inline]
    fn tick_list(&mut self, len: usize) -> bool {
        self.ticks += 1 + (len as u64) / 8;
        self.ticks >= self.limit
    }
}

impl Solver {
    /// Whether the chain factor is enabled (see [`factor_enabled_cfg`]).
    pub(super) fn factor_enabled(&self) -> bool {
        factor_enabled_cfg(&self.config)
    }

    /// One full factorization pass (kissat `kissat_factor` +
    /// `run_factorization`).  `round` is the 1-based eliminate-round
    /// counter (kissat `statistics.eliminations`, incremented at round
    /// entry); `window` is the search work since the last round (0 for the
    /// pre-search one-shot, which uses the initial budget).  Returns the
    /// number of introduced hub variables.  The caller owns the watch/BIG
    /// rebuild when the return is positive.
    pub(super) fn factor_pass(&mut self, round: u64, window: u64) -> usize {
        // Gates: every rewriting pass's contract (level 0, base scope, no
        // proof/LRAT, no real theory).
        if self.trail.decision_level() != 0
            || self.proof.is_some()
            || self.lrat
            || self.real_theory_attached
            || self.assertion_levels.len() > 1
            || self.trivially_unsat
        {
            return 0;
        }
        // kissat `kissat_factoring` delay: skip while
        // log10(active variables) > rounds + factordelay.
        let active = self.count_active_vars();
        if active > 0 {
            let log_active = (active as f64).log10() as u64;
            if log_active > round + FACTOR_DELAY {
                return 0;
            }
        }
        // kissat `limits.factor.marked`: skip entirely when no literal has
        // been marked since the last completed pass.
        if self.factor_marked_watermark >= self.factor_marked_total {
            return 0;
        }
        if self.propagate().is_some() {
            self.trivially_unsat = true;
            return 0;
        }
        self.stats.factor_passes += 1;

        // Cumulative budget (kissat: the first factorization gets
        // `factoriniticks`; later ones `factor_ticks + factoreffort‰ ×
        // max(window, mineffort)`).
        let delta = match factor_budget_override() {
            Some(t) => t,
            None if self.stats.factor_passes == 1 => FACTOR_INIT_TICKS,
            None => window
                .max(FACTOR_MIN_REFERENCE)
                .saturating_mul(FACTOR_EFFORT_PERMILLE)
                / 1000,
        };
        let limit = self.stats.factor_ticks.saturating_add(delta);

        let initial = (2 * self.num_vars) as u32;
        #[cfg(feature = "std")]
        if std::env::var("NIXIE_FACTOR_TRACE").is_ok() {
            let live_bins = self
                .clauses
                .iter_ids()
                .filter(|&cid| {
                    self.clauses
                        .get(cid)
                        .is_some_and(|c| !c.deleted && c.lits.len() == 2)
                })
                .count();
            let (big_edges, _) = self.binary_graph.edge_accounting();
            eprintln!(
                "factor_entry: live_binaries={live_bins} big_edges={big_edges} \
                 vars={} marks={}",
                self.num_vars, self.factor_marked_total
            );
        }
        let mut state = FactorState {
            quotients: Vec::new(),
            marks: vec![0; initial as usize],
            count: vec![0; initial as usize],
            counted: Vec::new(),
            nounted: Vec::new(),
            qmark: vec![false; self.clauses.num_slots()],
            qlauses: Vec::new(),
            dead: vec![false; self.clauses.num_slots()],
            dead_since_compact: 0,
            schedule: std::collections::BinaryHeap::new(),
            initial,
            fresh: Vec::new(),
            bound: 0,
            limit,
            ticks: 0,
            introduced: 0,
            pops: 0,
            processed: 0,
            links: 0,
            applies: 0,
            sum_m: 0,
            sum_n: 0,
        };
        // Occurrence index over candidate large clauses (dense-mode
        // `connect_clauses_to_factor`).
        let mut occ = self.build_factor_occurrence_index();

        // `schedule_factorization`: every dirty active literal with more
        // than one occurrence enters the heap (score = raw watch size —
        // kissat `update_candidate`).
        for code in 0..initial {
            let cu = code as usize;
            if cu >= self.factor_dirty.len() || !self.factor_dirty[cu] {
                continue;
            }
            if !self.lit_code_active(code) {
                continue;
            }
            let deg = self.factor_raw_degree(&occ, code);
            if deg > 1 {
                state.schedule.push((deg, code));
            }
        }

        // `run_factorization` main loop.
        while !state.schedule.is_empty() {
            let Some((_, code)) = state.schedule.pop() else {
                break;
            };
            if !self.lit_code_active(code) {
                continue;
            }
            // Cumulative tick check (kissat checks at the loop head).
            if state.ticks >= state.limit {
                break;
            }
            state.pops += 1;
            // Dirty-bit gate (kissat `f->factor & bit` + clear on use).
            if !self.factor_take_dirty(code) {
                continue;
            }
            state.processed += 1;
            // Grow the pass-local tables with the literal / clause id
            // spaces (mid-pass introductions; see the struct docs).
            let need = 2 * self.num_vars;
            if state.marks.len() < need {
                state.marks.resize(need, 0);
                state.count.resize(need, 0);
            }
            if state.qmark.len() < self.clauses.num_slots() {
                state.qmark.resize(self.clauses.num_slots(), false);
                state.dead.resize(self.clauses.num_slots(), false);
            }

            let first = Lit::from_code(code);
            let chain_trace = chain_trace_enabled(state.applies);
            let q0 = self.factor_first(&mut state, &occ, first);
            if chain_trace {
                eprintln!("chain: first={} q0={q0}", first.code());
            }
            if q0 > 1 {
                let mut ext = 0usize;
                while let Some((next, next_count)) = self.factor_next(&mut state, &occ) {
                    let Some(next) = next else { break };
                    if next_count < 2 {
                        if chain_trace {
                            eprintln!("  stopped: next_count={next_count} ext={ext}");
                        }
                        break;
                    }
                    if chain_trace && ext < 8 {
                        eprintln!("  ext={ext} next={} count={next_count}", next.code());
                    }
                    ext += 1;
                    state.links += 1;
                    self.factorize_next(&mut state, &occ, next);
                }
                if let Some((idx, reduction)) = factor_best_quotient(&state) {
                    if chain_trace {
                        eprintln!("  best_quotient idx={idx} reduction={reduction}");
                    }
                    if reduction > state.bound {
                        state.applies += 1;
                        state.sum_m += idx + 1;
                        state.sum_n += state.quotients[idx].clauses.len();
                        if chain_trace {
                            eprintln!(
                                "  APPLY m={} n={}",
                                idx + 1,
                                state.quotients[idx].clauses.len()
                            );
                        }
                        self.factor_apply(&mut state, &mut occ, idx);
                    }
                }
            }
            self.factor_release(&mut state);
        }

        let completed = state.schedule.is_empty();
        if completed {
            self.factor_marked_watermark = self.factor_marked_total;
        }
        self.factor_adjust_fresh(&mut state);
        self.stats.factor_ticks += state.ticks;
        self.stats.factor_introduced += state.introduced as u64;
        #[cfg(feature = "std")]
        if std::env::var("NIXIE_FACTOR_TRACE").is_ok() {
            eprintln!(
                "factor_pass: round={round} introduced={} ticks={} completed={completed} \
                 pops={} processed={} links={} applies={} avg_m={:.1} avg_n={:.1} \
                 fresh_total={}",
                state.introduced,
                state.ticks,
                state.pops,
                state.processed,
                state.links,
                state.applies,
                state.sum_m as f64 / state.applies.max(1) as f64,
                state.sum_n as f64 / state.applies.max(1) as f64,
                self.stats.factor_introduced
            );
        }
        state.introduced
    }

    /// Pre-search one-shot wrapper: the pass plus the watch/BIG rebuild its
    /// introductions and retirements leave stale, and a re-propagation
    /// (mid-search callers join `inprocess()`'s shared block instead).
    pub(super) fn factor_presearch(&mut self) -> usize {
        let n = self.factor_pass(1, 0);
        if n > 0 {
            self.rebuild_watches_and_binary_graph();
            if self.propagate().is_some() {
                // The pass never adds level-0 units (argued in the module
                // doc), so a conflict here certifies Unsat against live
                // clauses.
                self.trivially_unsat = true;
            }
        }
        n
    }

    /// Number of active (unassigned, non-eliminated) variables.
    fn count_active_vars(&self) -> usize {
        (0..self.num_vars)
            .filter(|&i| {
                let v = Var::new(i as u32);
                !self.trail.is_assigned(v) && !self.var_eliminated(v)
            })
            .count()
    }

    /// Active check by literal code (kissat `ACTIVE(idx)`).
    fn lit_code_active(&self, code: u32) -> bool {
        let v = Lit::from_code(code).var();
        (v.index() < self.num_vars) && !self.trail.is_assigned(v) && !self.var_eliminated(v)
    }

    /// Take (check-and-clear) the factor-dirty bit of `code` (kissat clears
    /// the flag bit when a literal is popped as a first pivot).
    fn factor_take_dirty(&mut self, code: u32) -> bool {
        let c = code as usize;
        if c >= self.factor_dirty.len() {
            return false;
        }
        if self.factor_dirty[c] {
            self.factor_dirty[c] = false;
            true
        } else {
            false
        }
    }

    /// Raw occurrence count of `code`: BIG adjacency (binaries containing
    /// the literal = edges from its negation) + large occurrence index
    /// (primary span + mid-pass overflow).  Snapshot semantics — tombstoned
    /// entries still count between compactions (divergence noted in the
    /// module doc; steering only).
    fn factor_raw_degree(&self, occ: &OccIndex, code: u32) -> u64 {
        let l = Lit::from_code(code);
        let big = self.binary_graph.get(l.negate()).len() as u64;
        big + occ.len(code) as u64 + occ.extra_len(code) as u64
    }

    /// Liveness check for a binary BIG edge via the tombstone bitset —
    /// O(1), no arena deref (tombstone retirements inside this pass are
    /// marked here; the BIG is compacted periodically, see
    /// [`Solver::factor_maybe_compact`]).  Ids beyond the pass's start
    /// snapshot are freshly added, hence live.
    #[inline]
    fn factor_edge_live(state: &FactorState, cid: ClauseId) -> bool {
        let c = cid.index();
        if c >= state.dead.len() {
            return true;
        }
        !state.dead[c]
    }

    /// Periodic BIG compaction (our analogue of kissat's eager O(1) watch
    /// removal): once tombstones accumulate, drop dead edges from the
    /// primary spans and overflow lists in one sweep so later scans walk
    /// only live entries.  Safe between rounds — no propagation runs on a
    /// tombstoned BIG (the caller rebuilds before re-propagating), and the
    /// per-code edge order is preserved.
    fn factor_maybe_compact(&mut self, state: &mut FactorState) {
        if state.dead_since_compact < FACTOR_COMPACT_THRESHOLD {
            return;
        }
        let dead: Vec<bool> = state.dead.clone();
        self.binary_graph.compact_dead(&dead);
        state.dead_since_compact = 0;
    }

    /// Liveness check for a candidate large clause.
    fn factor_large_live(&self, cid: ClauseId, state: &FactorState) -> bool {
        let slot = cid.index();
        if slot < state.dead.len() && state.dead[slot] {
            return false;
        }
        self.clauses.get(cid).is_some_and(|c| {
            !c.deleted && !c.learned && (3..=FACTOR_SIZE).contains(&c.lits.len())
        })
    }

    /// Build the large-clause occurrence index (kissat
    /// `connect_clauses_to_factor`): original clauses of size
    /// `3..=FACTOR_SIZE` where every literal has binary+large occurrence
    /// `≥ 2`, after `FACTOR_CAND_ROUNDS` fixed-point reduction rounds.
    fn build_factor_occurrence_index(&self) -> OccIndex {
        let num_lits = 2 * self.num_vars;
        // Binary occurrence per literal: BIG adjacency length (raw — no
        // retirements have happened inside this pass yet, so raw = live
        // here).
        let mut bincount = vec![0u32; num_lits];
        for code in 0..num_lits as u32 {
            let l = Lit::from_code(code);
            bincount[code as usize] = self.binary_graph.get(l.negate()).len() as u32;
        }
        // Candidate snapshot + per-literal large counts, iterated to the
        // fixed point (kissat `factorcandrounds`; the initial iteration
        // filters on binary counts only — a large clause participates only
        // in binary-rich neighborhoods by design).
        let mut largecount = vec![0u32; num_lits];
        let mut candidates: Vec<ClauseId> = Vec::new();
        for _round in 0..=FACTOR_CAND_ROUNDS {
            candidates.clear();
            for slot in largecount.iter_mut() {
                *slot = 0;
            }
            for cid in self.clauses.iter_ids() {
                let Some(c) = self.clauses.get(cid) else { continue };
                if c.learned || c.lits.len() < 3 || c.lits.len() > FACTOR_SIZE {
                    continue;
                }
                if c.lits
                    .iter()
                    .any(|l| bincount[l.code() as usize] + largecount[l.code() as usize] < 2)
                {
                    continue;
                }
                for &l in c.lits {
                    largecount[l.code() as usize] += 1;
                }
                candidates.push(cid);
            }
        }
        // Two-phase CSR fill (ids ascending within each span by iteration).
        let mut occ = OccIndex {
            span_end: vec![0; num_lits],
            flat: Vec::new(),
            extra: FxHashMap::default(),
        };
        for &cid in &candidates {
            if let Some(c) = self.clauses.get(cid) {
                for &l in c.lits {
                    occ.span_end[l.code() as usize] += 1;
                }
            }
        }
        let mut running = 0u32;
        for e in &mut occ.span_end {
            running += *e;
            *e = running;
        }
        occ.flat = vec![ClauseId::NULL; running as usize];
        let mut cursor = occ.span_end.clone();
        cursor.insert(0, 0);
        cursor.pop();
        for &cid in &candidates {
            if let Some(c) = self.clauses.get(cid) {
                for &l in c.lits {
                    let cu = l.code() as usize;
                    occ.flat[cursor[cu] as usize] = cid;
                    cursor[cu] += 1;
                }
            }
        }
        occ
    }

    /// kissat `first_factor`: quotient 0 = every live clause containing
    /// `factor` (binaries via the BIG, large candidates via the occurrence
    /// index).  Returns the clause count.
    fn factor_first(&mut self, state: &mut FactorState, occ: &OccIndex, factor: Lit) -> usize {
        debug_assert!(state.quotients.is_empty());
        let mut clauses: Vec<FEntry> = Vec::new();
        // Binaries `(factor ∨ q)`: BIG edges from `¬factor`.
        let edges: Vec<(Lit, ClauseId)> = self
            .binary_graph
            .get(factor.negate())
            .iter()
            .copied()
            .collect();
        for (q, cid) in edges {
            if q.var() == factor.var() || !Self::factor_edge_live(state, cid) {
                continue;
            }
            clauses.push(FEntry { q: Some(q), cid });
            state.tick();
        }
        // Large candidates containing `factor`.
        let mut larges: Vec<ClauseId> = Vec::new();
        occ.for_each(factor.code(), &mut |cid| larges.push(cid));
        for cid in larges {
            if self.factor_large_live(cid, state) {
                clauses.push(FEntry { q: None, cid });
            }
            state.tick();
        }
        let n = clauses.len();
        state.quotients.push(Quotient {
            factor: Some(factor),
            clauses,
            matches: Vec::new(),
        });
        state.marks[factor.code() as usize] |= MARK_FACTOR;
        n
    }

    /// Take the chain tail's clause list out of `state` (borrow hygiene:
    /// the scan interleaves `&mut state` counters with `&self` reads) and
    /// return it with the tail's factor.
    fn factor_take_tail(state: &mut FactorState) -> (Vec<FEntry>, Lit) {
        let last = state.quotients.last_mut().expect("chain tail exists");
        let factor = last.factor.expect("link factor");
        (core::mem::take(&mut last.clauses), factor)
    }

    /// Restore the chain tail's clause list after a scan.
    fn factor_restore_tail(state: &mut FactorState, entries: Vec<FEntry>) {
        let last = state.quotients.last_mut().expect("chain tail exists");
        last.clauses = entries;
    }

    /// kissat `next_factor`: count next-pivot candidates over the chain
    /// tail's clauses.  Returns `(winner, count)`; the winner is `None`
    /// when no candidate reaches count `≥ 2` (or the budget ran out).
    fn factor_next(&mut self, state: &mut FactorState, occ: &OccIndex) -> Option<(Option<Lit>, u32)> {
        if state.quotients.is_empty() {
            return None;
        }
        let (tail_entries, tail_factor) = Self::factor_take_tail(state);
        let initial = state.initial;
        debug_assert!(state.counted.is_empty());
        debug_assert!(state.nounted.is_empty());
        debug_assert!(state.qlauses.is_empty());

        let mut over_budget = false;
        for entry in &tail_entries {
            if !self
                .clauses
                .get(entry.cid)
                .is_some_and(|c| !c.deleted && c.lits.contains(&tail_factor))
            {
                continue;
            }
            match entry.q {
                Some(q) => {
                    // Binary tail clause `(x_k ∨ q)`: candidates are `q`'s
                    // binary partners — BIG edges from `¬q` are exactly the
                    // live binaries `(q ∨ next)` (kissat scans `q`'s binary
                    // watches).
                    let partners: Vec<(Lit, ClauseId)> = self
                        .binary_graph
                        .get(q.negate())
                        .iter()
                        .copied()
                        .collect();
                    if state.tick_list(partners.len()) {
                        over_budget = true;
                    }
                    for (next, wcid) in partners {
                        if next.var() == q.var() || !Self::factor_edge_live(state, wcid) {
                            continue;
                        }
                        if next.code() >= initial || !self.lit_code_active(next.code()) {
                            continue;
                        }
                        if state.marks[next.code() as usize] & MARK_FACTOR != 0 {
                            continue;
                        }
                        let nc = next.code() as usize;
                        if state.count[nc] == 0 {
                            state.counted.push(next.code());
                        }
                        state.count[nc] += 1;
                    }
                }
                None => {
                    // Large tail clause `(x_k ∨ A)`: scan the
                    // minimum-degree non-factor literal's occurrence list
                    // for same-size clauses `d = (next ∨ A)`.
                    let Some(cview) = self.clauses.get(entry.cid) else {
                        continue;
                    };
                    let clits: SmallVec<[Lit; 8]> = cview.lits.iter().copied().collect();
                    let c_size = clits.len();
                    let mut min_lit: Option<Lit> = None;
                    let mut min_size = u64::MAX;
                    let mut factors = 0usize;
                    let mut quotient_marked: SmallVec<[Lit; 8]> = SmallVec::new();
                    for &l in &clits {
                        if state.marks[l.code() as usize] & MARK_FACTOR != 0 {
                            factors += 1;
                            if factors > 1 {
                                break;
                            }
                        } else {
                            state.marks[l.code() as usize] |= MARK_QUOTIENT;
                            quotient_marked.push(l);
                            let sz = self.factor_raw_degree(occ, l.code());
                            if min_lit.is_none() || sz < min_size {
                                min_lit = Some(l);
                                min_size = sz;
                            }
                        }
                    }
                    if factors == 1
                        && let Some(min_lit) = min_lit
                    {
                        let mut occs: Vec<ClauseId> = Vec::new();
                        occ.for_each(min_lit.code(), &mut |cid| occs.push(cid));
                        if state.tick_list(occs.len()) {
                            over_budget = true;
                        }
                        for d_cid in occs {
                            if d_cid == entry.cid || state.qmark[d_cid.index()] {
                                continue;
                            }
                            let Some(d) = self.clauses.get(d_cid) else {
                                continue;
                            };
                            if d.deleted || d.lits.len() != c_size {
                                continue;
                            }
                            // `d` must be `(A ∖ {x_k}) ∪ {next}` for exactly
                            // one new literal `next` (kissat's mark walk).
                            let mut next: Option<Lit> = None;
                            let mut reject = false;
                            for &l in d.lits.iter() {
                                let m = state.marks[l.code() as usize];
                                if m & MARK_QUOTIENT != 0 {
                                    continue;
                                }
                                if m & MARK_FACTOR != 0 || m & MARK_NOUNTED != 0 {
                                    reject = true;
                                    break;
                                }
                                if next.is_some() {
                                    reject = true;
                                    break;
                                }
                                next = Some(l);
                            }
                            if reject {
                                continue;
                            }
                            let Some(next) = next else { continue };
                            if next.code() >= initial || !self.lit_code_active(next.code()) {
                                continue;
                            }
                            let nc = next.code() as usize;
                            debug_assert!(state.marks[nc] & (MARK_FACTOR | MARK_NOUNTED) == 0);
                            state.marks[nc] |= MARK_NOUNTED;
                            state.nounted.push(next.code());
                            state.qmark[d_cid.index()] = true;
                            state.qlauses.push(d_cid.index());
                            if state.count[nc] == 0 {
                                state.counted.push(next.code());
                            }
                            state.count[nc] += 1;
                        }
                    }
                    // Clear this clause's marks (kissat clears NOUNTED per
                    // clause and QUOTIENT at the clause end).
                    for code in state.nounted.drain(..) {
                        state.marks[code as usize] &= !MARK_NOUNTED;
                    }
                    for l in quotient_marked {
                        state.marks[l.code() as usize] &= !MARK_QUOTIENT;
                    }
                }
            }
            if state.tick() {
                over_budget = true;
            }
            if over_budget {
                break;
            }
        }
        Self::factor_restore_tail(state, tail_entries);
        // Clear the clause-dedup bits of this call (kissat `clear_qlauses`).
        for idx in state.qlauses.drain(..) {
            state.qmark[idx] = false;
        }

        // Winner selection (kissat: only when the ticks limit holds; max
        // count, first-seen wins; ties broken by `watches_score` with
        // `factorstructural=0`).
        let mut next: Option<Lit> = None;
        let mut next_count = 0u32;
        let mut ties = 0u32;
        if !over_budget {
            for &code in &state.counted {
                let cnt = state.count[code as usize];
                if cnt < next_count {
                    continue;
                }
                if cnt == next_count {
                    ties += 1;
                } else {
                    next_count = cnt;
                    next = Some(Lit::from_code(code));
                    ties = 1;
                }
            }
            if next_count < 2 {
                next = None;
            } else if ties > 1 {
                let mut best: Option<(u64, Lit)> = None;
                for &code in &state.counted {
                    if state.count[code as usize] != next_count {
                        continue;
                    }
                    let score = self.factor_raw_degree(occ, code);
                    if best.is_none_or(|(s, _)| score > s) {
                        best = Some((score, Lit::from_code(code)));
                    }
                }
                next = best.map(|(_, l)| l);
            }
        }
        for &code in &state.counted {
            state.count[code as usize] = 0;
        }
        state.counted.clear();
        Some((next, next_count))
    }

    /// kissat `factorize_next`: build the next link's matched clause list
    /// for pivot `next` (the same scans as [`Self::factor_next`], but
    /// recording survivors and their `matches` indices).
    fn factorize_next(&mut self, state: &mut FactorState, occ: &OccIndex, next: Lit) {
        if state.quotients.is_empty() {
            return;
        }
        let (tail_entries, tail_factor) = Self::factor_take_tail(state);
        state.marks[next.code() as usize] |= MARK_FACTOR;
        let mut new_clauses: Vec<FEntry> = Vec::new();
        let mut new_matches: Vec<u32> = Vec::new();

        for (i, entry) in tail_entries.iter().enumerate() {
            if !self
                .clauses
                .get(entry.cid)
                .is_some_and(|c| !c.deleted && c.lits.contains(&tail_factor))
            {
                continue;
            }
            match entry.q {
                Some(q) => {
                    // Binary tail clause `(x_k ∨ q)`: match witness is the
                    // binary `(q ∨ next)`.
                    let partners: Vec<(Lit, ClauseId)> = self
                        .binary_graph
                        .get(q.negate())
                        .iter()
                        .copied()
                        .collect();
                    state.tick_list(partners.len());
                    for (pl, wcid) in partners {
                        if pl == next && Self::factor_edge_live(state, wcid) {
                            // The new link's entry names the witness (it
                            // contains the NEW factor).
                            new_clauses.push(FEntry {
                                q: Some(q),
                                cid: wcid,
                            });
                            new_matches.push(i as u32);
                            break;
                        }
                    }
                }
                None => {
                    let Some(cview) = self.clauses.get(entry.cid) else {
                        continue;
                    };
                    let clits: SmallVec<[Lit; 8]> = cview.lits.iter().copied().collect();
                    let c_size = clits.len();
                    let mut min_lit: Option<Lit> = None;
                    let mut min_size = u64::MAX;
                    let mut quotient_marked: SmallVec<[Lit; 8]> = SmallVec::new();
                    for &l in &clits {
                        if state.marks[l.code() as usize] & MARK_FACTOR != 0 {
                            continue;
                        }
                        state.marks[l.code() as usize] |= MARK_QUOTIENT;
                        quotient_marked.push(l);
                        let sz = self.factor_raw_degree(occ, l.code());
                        if min_lit.is_none() || sz < min_size {
                            min_lit = Some(l);
                            min_size = sz;
                        }
                    }
                    if let Some(min_lit) = min_lit {
                        let mut occs: Vec<ClauseId> = Vec::new();
                        occ.for_each(min_lit.code(), &mut |cid| occs.push(cid));
                        state.tick_list(occs.len());
                        for d_cid in occs {
                            if d_cid == entry.cid || state.qmark[d_cid.index()] {
                                continue;
                            }
                            let Some(d) = self.clauses.get(d_cid) else {
                                continue;
                            };
                            if d.deleted || d.lits.len() != c_size {
                                continue;
                            }
                            // `d`'s literals must all be QUOTIENT-marked
                            // (shared with the tail clause) or `next`.
                            let mut matched = true;
                            for &l in d.lits.iter() {
                                let m = state.marks[l.code() as usize];
                                if m & MARK_QUOTIENT != 0 {
                                    continue;
                                }
                                if l != next {
                                    matched = false;
                                    break;
                                }
                            }
                            if matched {
                                new_clauses.push(FEntry {
                                    q: None,
                                    cid: d_cid,
                                });
                                new_matches.push(i as u32);
                                state.qmark[d_cid.index()] = true;
                                state.qlauses.push(d_cid.index());
                                break;
                            }
                        }
                    }
                    for l in quotient_marked {
                        state.marks[l.code() as usize] &= !MARK_QUOTIENT;
                    }
                }
            }
        }
        // Restore the tail (unchanged) and clear this call's dedup bits.
        Self::factor_restore_tail(state, tail_entries);
        for idx in state.qlauses.drain(..) {
            state.qmark[idx] = false;
        }
        state.quotients.push(Quotient {
            factor: Some(next),
            clauses: new_clauses,
            matches: new_matches,
        });
    }

    /// kissat `release_quotients`: clear FACTOR marks and drop the chain.
    fn factor_release(&mut self, state: &mut FactorState) {
        for q in &state.quotients {
            if let Some(f) = q.factor {
                state.marks[f.code() as usize] &= !MARK_FACTOR;
            }
        }
        state.quotients.clear();
        debug_assert!(state.counted.is_empty());
        debug_assert!(state.nounted.is_empty());
        debug_assert!(state.qlauses.is_empty());
    }

    /// Apply the chain cut at `idx` (kissat `apply_factoring`).  Skips
    /// (without introducing) when any chain clause is a live propagation
    /// reason — our mid-search hygiene invariant (kissat's dense-mode
    /// deletion needs no such check).
    fn factor_apply(&mut self, state: &mut FactorState, occ: &mut OccIndex, idx: usize) {
        for q in &state.quotients[..=idx] {
            for e in &q.clauses {
                if let Some(c) = self.clauses.get(e.cid)
                    && !c.deleted
                    && self.is_live_reason_clause(e.cid, c.lits)
                {
                    return; // skip; the pass continues with the next pivot
                }
            }
        }

        // `flush_unmatched_clauses`: compact every link below `idx` to the
        // matched pattern set.  Walking `idx → 1` keeps each link's
        // `matches` aligned with its already-compacted predecessor
        // (kissat's `POKE` chains).
        for k in (1..=idx).rev() {
            let n = state.quotients[k].clauses.len();
            for i in 0..n {
                let j = state.quotients[k].matches[i] as usize;
                let e = state.quotients[k - 1].clauses[j];
                state.quotients[k - 1].clauses[i] = e;
                if k >= 2 {
                    let mj = state.quotients[k - 1].matches[j];
                    state.quotients[k - 1].matches[i] = mj;
                }
            }
            state.quotients[k - 1].clauses.truncate(n);
            if k >= 2 {
                state.quotients[k - 1].matches.truncate(n);
            }
        }

        let t = Lit::pos(self.new_var());
        state.fresh.push(t.var());

        // Dividers `(t ∨ x_i)` per link (kissat `add_factored_divider`).
        let factors: SmallVec<[Lit; 8]> = state.quotients[..=idx]
            .iter()
            .map(|q| q.factor.expect("link factor"))
            .collect();
        for &factor in &factors {
            self.factor_add_binary(state, t, factor);
        }
        // Quotients `(¬t ∨ A_j)` from the best link's matched clauses
        // (kissat `add_factored_quotient`).
        let not_t = t.negate();
        let best_factor = state.quotients[idx].factor.expect("link factor");
        let best_entries: Vec<FEntry> = state.quotients[idx].clauses.clone();
        for e in &best_entries {
            match e.q {
                Some(q) => self.factor_add_binary(state, not_t, q),
                None => {
                    if let Some(c) = self.clauses.get(e.cid)
                        && !c.deleted
                    {
                        let mut lits: SmallVec<[Lit; 8]> = SmallVec::with_capacity(c.lits.len());
                        lits.push(not_t);
                        for &l in c.lits.iter() {
                            if l != best_factor {
                                lits.push(l);
                            }
                        }
                        self.factor_add_large(state, occ, &lits);
                    }
                }
            }
        }
        // Delete every chain clause (kissat `delete_unfactored`; our
        // retirement is the tombstone + periodic compaction — the caller
        // rebuilds BIG/watches, and reads inside this pass validate
        // liveness).
        let mut touched: SmallVec<[Lit; 32]> = SmallVec::new();
        touched.push(t);
        touched.push(not_t);
        let chain_entries: Vec<FEntry> = state.quotients[..=idx]
            .iter()
            .flat_map(|q| q.clauses.iter().copied())
            .collect();
        for e in chain_entries {
            if let Some(c) = self.clauses.get(e.cid)
                && !c.deleted
            {
                touched.extend(c.lits.iter().copied());
                self.clauses.remove(e.cid);
                let slot = e.cid.index();
                if slot < state.dead.len() {
                    state.dead[slot] = true;
                }
                state.dead_since_compact += 1;
                state.tick();
                self.stats.factor_clauses_rewritten += 1;
            }
        }
        // `update_factored`: re-arm the schedule for the chain literals —
        // each factor in BOTH polarities plus the deleted clauses'
        // literals, exactly kissat's set.  The fresh hub `t` is
        // deliberately NOT pushed (kissat never pushes it either): hubs
        // must not be factored against each other inside the pass —
        // hub-on-hub chains build mega-clusters whose conflict clauses
        // span thousands of levels (measured avg_lbd 1103 on worker_550
        // before this exclusion; the handover's calibration shows kissat
        // at decisions/conflict ≈ 227, not thousands).
        for &f in &factors {
            for l in [f, f.negate()] {
                if l.code() < state.initial {
                    let deg = self.factor_raw_degree(occ, l.code());
                    if deg > 1 {
                        state.schedule.push((deg, l.code()));
                    }
                }
            }
        }
        for &l in &touched {
            if l.var() == t.var() {
                continue;
            }
            if l.code() < state.initial {
                let deg = self.factor_raw_degree(occ, l.code());
                if deg > 1 {
                    state.schedule.push((deg, l.code()));
                }
            }
        }
        self.mark_elim_vars(touched.iter().copied());
        self.factor_maybe_compact(state);
        state.introduced += 1;
    }

    /// Add a factor binary `(a ∨ b)` with immediate BIG connection and
    /// dirty marking (kissat `kissat_new_binary_clause`).
    fn factor_add_binary(&mut self, state: &mut FactorState, a: Lit, b: Lit) {
        let cid = self.clauses.add_original([a, b]);
        self.binary_graph.add(a.negate(), b, cid);
        self.binary_graph.add(b.negate(), a, cid);
        self.mark_subsume_lits([a, b].iter());
        state.tick();
        self.stats.factor_clauses_rewritten += 1;
    }

    /// Add a factor quotient clause (≥ 3 literals) with immediate
    /// occurrence-index connection (kissat's dense-mode connect).
    fn factor_add_large(
        &mut self,
        state: &mut FactorState,
        occ: &mut OccIndex,
        lits: &SmallVec<[Lit; 8]>,
    ) {
        let cid = self.clauses.add_original(lits.iter().copied());
        for &l in lits {
            if l.code() < state.initial {
                occ.push(l.code(), cid);
            }
        }
        self.mark_subsume_lits(lits.iter());
        state.tick();
        self.stats.factor_clauses_rewritten += 1;
    }

    /// kissat `adjust_scores_and_phases_of_fresh_variables`.  VSIDS: our
    /// `new_var` inserts at activity 0 (kissat zeroes its ≈1 activation
    /// score) — nothing to do.  VMTF: fresh variables move to the oldest
    /// end and the list is restamped (`NIXIE_FACTOR_SCHED` arms).
    fn factor_adjust_fresh(&mut self, state: &mut FactorState) {
        if state.fresh.is_empty() {
            return;
        }
        match factor_sched_mode() {
            FactorSched::Back => self.vmtf.enqueue_oldest_and_restamp(&state.fresh),
            FactorSched::Front => {
                for &v in &state.fresh {
                    self.vmtf.bump(v, |v| self.trail.is_assigned(v));
                }
            }
            FactorSched::Leave => {}
        }
    }
}

/// kissat `best_quotient` (free function over the state): best prefix cut
/// by reduction `n·(p+1) − n − (p+1)`; the first maximum wins.
fn factor_best_quotient(state: &FactorState) -> Option<(usize, i64)> {
    let mut best: Option<(usize, i64)> = None;
    for (p, q) in state.quotients.iter().enumerate() {
        let factors = (p + 1) as i64;
        let n = q.clauses.len() as i64;
        let before = n * factors;
        let after = n + factors;
        if before <= after {
            continue;
        }
        let delta = before - after;
        if best.is_none_or(|(_, b): (usize, i64)| delta > b) {
            best = Some((p, delta));
        }
    }
    best
}
