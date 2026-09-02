//! CDCL SAT Solver

mod bva;
mod bve;
mod conflict;
mod congruence;
mod decide;
mod eliminate;
mod equiv;
pub mod heuristic;
mod incremental;
mod learn;
mod lucky;
mod probe;
mod propagate;
mod search_ext;
mod subsume;
mod transred;
mod walk;

pub use heuristic::{BoxedBranchingHeuristic, BranchingHeuristic};

use crate::chb::CHB;
use crate::chrono::ChronoBacktrack;
use crate::clause::{ClauseDatabase, ClauseId};
use crate::literal::{LBool, Lit, Var};
use crate::lrb::LRB;
use crate::memory_opt::{MemoryAction, MemoryOptimizer};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::restart_model::{GlueAverages, Reluctant};
use crate::trail::{Reason, Trail};
use crate::vmtf::VMTF;
use crate::vsids::VSIDS;
use crate::watched::{WatchLists, Watcher};
use core::sync::atomic::{AtomicBool, Ordering};
use smallvec::SmallVec;

/// One 64-position chunk of the shrink scan's `MF_SHRINKABLE` summary
/// (see [`Solver::shrink_summary`]).
#[derive(Debug, Clone, Copy)]
pub(super) struct ShrinkChunk {
    /// Block epoch this `bits` word belongs to; anything else reads as empty.
    pub(super) epoch: u64,
    /// Bit `i` set iff the literal at trail position `chunk*64 + i` is
    /// flagged `MF_SHRINKABLE` in that block. Exact within the block:
    /// every marking site sets it, the flagged set only grows, positions
    /// never move.
    pub(super) bits: u64,
}

impl ShrinkChunk {
    /// Fresh entry: epoch 0 is never a valid block epoch (the counter
    /// starts at 1 after the first bump), so `bits` is never consulted.
    pub(super) const EMPTY: ShrinkChunk = ShrinkChunk { epoch: 0, bits: 0 };
}

// Packed per-variable LRAT minimization flags (`Flags` in upstream), stored
// in [`Solver::lrat_flags`] indexed by `Var::index()`. The bit layout mirrors
// cadical's `Flags` fields used by `minimize.cpp`.
pub(super) const MF_KEEP: u8 = 1;
pub(super) const MF_POISON: u8 = 2;
pub(super) const MF_REMOVABLE: u8 = 4;
pub(super) const MF_ADDED: u8 = 8;
pub(super) const MF_SEEN: u8 = 16;
pub(super) const MF_SHRINKABLE: u8 = 32;

/// Convert a path to a UTF-8 string for the file tracers (which take `&str`,
/// faithful to upstream). Returns an error for non-UTF8 paths.
fn path_to_str(path: &std::path::Path) -> std::io::Result<&str> {
    path.to_str().ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "proof file path must be valid UTF-8",
        )
    })
}

/// Binary implication graph for efficient binary clause propagation
/// For each literal L, stores the list of literals that are implied when L is false
/// (i.e., for binary clause (~L v M), when L is assigned false, M must be true)
/// Initial `lim.inprobe`: the first probe round fires once conflicts reach
/// the base interval (mirrors how `lim_elim` initializes from the config).
/// Initial probe-round conflict limit before the first solve re-derives it
/// from the formula size (see `init_rephase_limits`). Zero makes `inprobing`
/// never fire before a solve ran – probing mid-search only ever makes sense
/// after `init_rephase_limits` has sized the schedule to the input.
const INPROBE_INIT_LIMIT: u64 = u64::MAX;

#[derive(Debug, Clone)]
pub(super) struct BinaryImplicationGraph {
    /// implications[lit] = list of (implied_lit, clause_id) pairs
    implications: Vec<Vec<(Lit, ClauseId)>>,
}

impl BinaryImplicationGraph {
    fn new(num_vars: usize) -> Self {
        Self {
            implications: vec![Vec::new(); num_vars * 2],
        }
    }

    /// Total live edges and their allocation slack (diagnostics:
    /// `OXIZ_MEM_STATS`). The BIG is the propagation backbone for binaries
    /// and, unlike the clause arena, has no compaction — its footprint is
    /// live edges plus each per-literal Vec's doubling overshoot.
    pub(crate) fn edge_accounting(&self) -> (usize, usize) {
        let edges: usize = self.implications.iter().map(Vec::len).sum();
        let cap: usize = self.implications.iter().map(Vec::capacity).sum();
        (edges, cap)
    }

    fn resize(&mut self, num_vars: usize) {
        self.implications.resize(num_vars * 2, Vec::new());
    }

    fn add(&mut self, lit: Lit, implied: Lit, clause_id: ClauseId) {
        self.implications[lit.code() as usize].push((implied, clause_id));
    }

    /// Owned edge list of `lit`'s trigger (for the take/put-back pattern in
    /// propagation).
    fn get_mut(&mut self, lit: Lit) -> &mut Vec<(Lit, ClauseId)> {
        let idx = lit.code() as usize;
        if idx >= self.implications.len() {
            self.implications.resize(idx + 1, Vec::new());
        }
        &mut self.implications[idx]
    }

    pub(crate) fn get(&self, lit: Lit) -> &[(Lit, ClauseId)] {
        &self.implications[lit.code() as usize]
    }

    /// Iterate every edge as `(trigger, implied, clause_id)`, in key order.
    /// Debug-invariant use (BIG-authoritative BCP backing check): the hot
    /// loop trusts edges without a liveness probe, so every non-sentinel
    /// edge must reference a live binary clause.
    pub(crate) fn iter(&self) -> impl Iterator<Item = (Lit, Lit, ClauseId)> + '_ {
        self.implications
            .iter()
            .enumerate()
            .flat_map(|(code, list)| {
                let from = Lit::from_code(code as u32);
                list.iter().map(move |&(to, cid)| (from, to, cid))
            })
    }

    fn clear(&mut self) {
        for implications in &mut self.implications {
            implications.clear();
        }
    }

    /// Remove every edge belonging to `clause_id` that is keyed under `trigger`.
    /// Used to purge binary implications when a clause is retracted so the graph
    /// does not accumulate stale (and, after slot reuse, misleading) edges.
    fn remove_clause_edges(&mut self, trigger: Lit, clause_id: ClauseId) {
        let idx = trigger.code() as usize;
        if idx < self.implications.len() {
            self.implications[idx].retain(|(_, cid)| *cid != clause_id);
        }
    }
}

/// Result from a theory check
#[derive(Debug, Clone)]
pub enum TheoryCheckResult {
    /// Theory is satisfied under current assignment
    Sat,
    /// Theory detected a conflict, returns conflict clause literals
    Conflict(SmallVec<[Lit; 8]>),
    /// Theory propagated new literals (lit, reason clause)
    Propagated(Vec<(Lit, SmallVec<[Lit; 8]>)>),
}

/// Callback trait for theory solvers
/// The CDCL(T) solver implements this to receive theory callbacks
pub trait TheoryCallback {
    /// Called when a literal is assigned
    /// Returns a theory check result
    fn on_assignment(&mut self, lit: Lit) -> TheoryCheckResult;

    /// Called after propagation is complete to do a full theory check
    fn final_check(&mut self) -> TheoryCheckResult;

    /// Called when the decision level increases
    fn on_new_level(&mut self, _level: u32) {}

    /// Called when backtracking
    fn on_backtrack(&mut self, level: u32);

    /// Whether this callback carries *theory* constraints beyond the Boolean
    /// clause set.
    ///
    /// This is a soundness signal, not a capability flag.  Pure-literal
    /// elimination inside `Solver::inprocess` deletes original clauses on
    /// the promise that the pure variable can be pinned to one polarity
    /// without loss.  In a pure SAT search every clause added later is
    /// *entailed* by the current set, so the promise holds.  A real theory
    /// callback breaks it: theory lemmas and propagations can legitimately
    /// force the opposite polarity of a variable whose Boolean occurrences
    /// are one-sided, and `save_model`'s pure-literal reconstruction would
    /// then hand back a model the theory never blessed.  The default
    /// (`false`, e.g. the no-op callback [`Solver::solve`] uses) keeps
    /// inprocessing fully enabled; real theory callbacks return `true` and
    /// `Solver::inprocess` skips only the pure-literal pass (subsumption
    /// and strengthening are entailment-based and stay sound either way).
    fn is_real_theory(&self) -> bool {
        false
    }
}

/// Result of SAT solving
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverResult {
    /// Satisfiable
    Sat,
    /// Unsatisfiable
    Unsat,
    /// Unknown (e.g., timeout, resource limit)
    Unknown,
}

/// Outcome of [`Solver::pre_check_effective_unit`], resolved *before* any
/// watches are chosen for a new clause in [`Solver::add_clause`].
enum PreAttachOutcome {
    /// Already satisfied by the current assignment, or simply not
    /// effectively unit (2+ literals still undefined). Either way, nothing
    /// special is needed: add and watch the clause normally.
    Ordinary,
    /// Every literal is false and, after resolving level-0-only facts via
    /// [`Solver::backtrack_to_root`] where needed, still is: an
    /// unconditional (level-0) conflict. The caller must set
    /// `trivially_unsat` and return `false` without adding the clause.
    UnconditionalConflict,
    /// The clause is an effective unit (every literal false except this one,
    /// which is undefined) and every false literal is confirmed to be a
    /// permanent level-0 fact. The caller must force this literal via
    /// `Trail::assign_propagation_at(_, clause_id, 0)` once the clause has
    /// been inserted and its `ClauseId` is known (not yet, at the point this
    /// outcome is produced).
    ForceUnitAtLevelZero(Lit),
}

/// Solver configuration
#[derive(Clone)]
pub struct SolverConfig {
    /// Restart interval (number of conflicts)
    pub restart_interval: u64,
    /// Restart multiplier for geometric restarts
    pub restart_multiplier: f64,
    /// Clause deletion threshold
    pub clause_deletion_threshold: usize,
    /// Variable decay factor
    pub var_decay: f64,
    /// Clause decay factor
    pub clause_decay: f64,
    /// Random polarity probability (0.0 to 1.0)
    pub random_polarity_prob: f64,
    /// Random-polarity probability override while in **stable** mode
    /// (cadical parity: random decisions default OFF and phase guidance is
    /// a stable-mode mechanism — target phases; the standing-gap loss-class
    /// files are model-finding instances where 2 % random polarity provably
    /// breaks phase-guided descent).  `None` ⇒ same as
    /// `random_polarity_prob` (the historical behaviour).
    pub random_polarity_prob_stable: Option<f64>,
    /// Restart strategy: "luby" or "geometric"
    pub restart_strategy: RestartStrategy,
    /// Enable lazy hyper-binary resolution
    pub enable_lazy_hyper_binary: bool,
    /// Use CHB instead of VSIDS for branching
    pub use_chb_branching: bool,
    /// Use LRB (Learning Rate Branching) for branching
    pub use_lrb_branching: bool,
    /// Enable inprocessing (periodic preprocessing during search)
    pub enable_inprocessing: bool,
    /// Enable equivalent-literal substitution (SCC on the binary implication
    /// graph) as a one-shot pre-search pass. Sound and well-tested (50k+
    /// differential fuzz vs the un-substituted path), but OFF by default: it
    /// folds equivalent variables out of the search, which is incompatible with
    /// incremental/AllSAT clients that reference original variables between
    /// solve() calls, and on the one structured benchmark with many
    /// equivalences (`longmult15`, 29% of vars in SCCs) it does not help –
    /// CaDiCaL's edge there is pure search quality, not structural collapse.
    /// Enable for one-shot solving of binary-heavy formulas where collapsing
    /// equivalences is expected to pay off.
    pub enable_equiv_substitution: bool,
    /// Whether equivalent-literal substitution augments the binary
    /// implication graph with congruences inferred from AND/XOR gates
    /// (multiplier / adder structure) before SCC. Default `true`.
    pub enable_gate_congruence: bool,
    /// Enable bounded variable elimination (BVE / SatELite) as a one-shot
    /// pre-search pass. Eliminates variables by resolving their clauses when
    /// the resolvents don't grow the formula, with model reconstruction. The
    /// most foundational SAT preprocessing technique. Off by default (same
    /// incremental/AllSAT caveat as substitution).
    pub enable_bve: bool,
    /// Structured bounded variable addition (k-way common-literal-set
    /// extraction, pre-search slice; `solver/bva.rs`).  Default off: this
    /// is a first slice pending its corpus study — see
    /// `docs/studies/2026-08-sbva.md`.  Experiment knob `OXIZ_SBVA=1`
    /// (and `OXIZ_SBVA_NULL=1` for the matched-null arm).
    pub enable_sbva: bool,
    /// Inprocessing interval (number of conflicts between inprocessing)
    pub inprocessing_interval: u64,
    /// Conflict interval between elimination phases (cadical `elimint`,
    /// default 2000). The next phase is additionally gated on new units or
    /// newly marked variables, and the interval grows with the phase count
    /// (`elimint * (phases + 1)`).
    pub elim_interval: u64,
    /// Enable chronological backtracking
    pub enable_chronological_backtrack: bool,
    /// cadical `chronoreusetrail`: on a short jump, stop above the
    /// best-bumped variable of the discarded region to keep trail content
    /// (`analyze.cpp::determine_actual_backtrack_level`).  Requires the
    /// level-filtered trail (landed with it).  Default **off**: cadical
    /// defaults it on, but our measurements are neutral-to-slightly-negative
    /// (single-seed tracking 0.92× paired, bimodal per file; 10-seed null
    /// study p=0.14) — see
    /// docs/studies/2026-08-chronoreusetrail-rejected.md.  Revisit with a
    /// full multi-seed study before flipping.
    pub chrono_reuse: bool,
    /// Late-enable gate for `chrono_reuse` (cadical `chronoreusetrail`):
    /// reuse stops fire only once the search has seen this many conflicts.
    /// **Measured dead as a default** (standing-gap study, 2026-08-21):
    /// the ungated port's residue wins need reuse from conflict 0 — a
    /// 400 k gate captured 0/25 residue files while still flipping (and
    /// losing) noL, whose default trajectory runs 1.5 M conflicts.  Kept
    /// as A/B infrastructure with `OXIZ_CHRONO_REUSE_AFTER`;
    /// `0` = always active when `chrono_reuse` is on.
    pub chrono_reuse_after: u64,
    /// Debug knob (`OXIZ_CHRONO_ALWAYS=1`): force chronological backtracking
    /// on every non-unit conflict (cadical `chronoalways`).  Exercises the
    /// out-of-order trail paths far more densely than the distance-threshold
    /// heuristic does.
    #[doc(hidden)]
    pub chrono_always: bool,
    /// Run the inprocessing passes as an unconditional **pre-search
    /// collapse** (BVE fixpoint, ELS one-shot, inprocess/vivify pre-passes)
    /// instead of deferring them to the conflict schedule.  Default `false`
    /// (cadical parity: CaDiCaL schedules every pass on the conflict clock —
    /// its first elimination lands around 1e4 conflicts — so instances that
    /// solve early never pay for or get structurally damaged by the passes;
    /// measured on ITC2021_Early_3: cadical eliminates zero variables and
    /// finishes in 1164 conflicts, our pre-search collapse eliminated 1903
    /// and needed 5040; with conflict scheduling the stack matches the
    /// default exactly there and keeps its hard-file wins, 48/60 paired
    /// files faster, geomean 6.3×, sign p<1e-4 over 10 seeds — see
    /// docs/studies/2026-08-inprocessing-schedule.md).
    pub presearch_collapse: bool,
    /// Chronological backtracking threshold (max distance from assertion level)
    pub chrono_backtrack_threshold: u32,
    /// Cap on the Luby restart multiplier. The Luby sequence grows as 2^k, so
    /// without a cap the restart interval explodes on long runs into
    /// multi-10k-conflict grinds (a 3-30x slowdown vs cadical on r3sat
    /// n300/n350). 0 = uncapped (legacy). Default caps at 1024× the base
    /// restart interval.
    pub luby_cap: u64,
    /// Enable the cadical-style stable/focused restart schedule: alternate
    /// focused mode (frequent restarts, `focused_luby_cap`) and stable mode
    /// (rare restarts + rephase) on a quadratically-growing conflict schedule.
    /// Default true. Makes restart aggressiveness adaptive to the instance
    /// instead of a single fixed cap.
    pub enable_stabilize: bool,
    /// Enable clause **shrinking** (cadical `opts.shrink == 3`, its default):
    /// per decision-level block of the raw 1-UIP clause, run a mini 1-UIP
    /// analysis restricted to that level and replace the whole block by its
    /// block-UIP literal (`shrink.cpp`).  This is cadical's default learned-
    /// clause improvement and supersedes plain recursive minimization there
    /// (the minimizer remains the in-block fallback and the LRAT path).
    /// Default true (cadical parity; measured before landing – see
    /// `docs/studies/`).
    pub enable_shrink: bool,
    /// Base conflict interval for the first stable/focused switch; subsequent
    /// intervals grow quadratically (`base × phase²`).
    pub stabilize_base: u64,
    /// Luby restart cap used in *focused* mode (frequent restarts). Stable
    /// mode restarts uncapped (rare). 0 = uncapped.
    pub focused_luby_cap: u64,
    /// Use VMTF (variable move-to-front) as the decision heuristic instead
    /// of VSIDS – cadical's default focused-mode branching.
    pub use_vmtf: bool,
    /// Use the cadical focused-mode VMTF scores under the stable/focused
    /// schedule (VMTF while focused, VSIDS while stable).  `false` runs VSIDS
    /// in both modes – the z3 `smt_context` behaviour, which suits CDCL(T):
    /// theory-aware branching benefit accumulates across mode switches, and
    /// VMTF's move-to-front bursts lose focus on theory-propagated variables.
    /// Pure-SAT callers keep the default `true` (cadical parity).
    pub focused_vmtf: bool,
    /// Use VMTF (variable move-to-front) as the decision heuristic instead of
    /// VSIDS – cadical's default focused-mode branching. Conflict-involved
    /// variables are moved to the tail of a list; the next decision is the
    /// most-recently-bumped unassigned variable.
    ///
    /// Rephasing (cadical `opts.rephase`): periodically overwrite the saved
    /// phases with one of a fixed schedule of strategies (best / inverted /
    /// flipping / random / original / walk), so a fresh restart explores a
    /// complementary phase region instead of re-deriving the previous trail.
    /// 0 = off, 1 = both stable and focused mode, 2 = stable mode only.
    /// Default 1 (cadical parity).
    pub rephase: u32,
    /// Rephase interval base (cadical `opts.rephaseint`, in conflicts). The
    /// next rephase fires after `rephase_interval × (rephase_count + 1)`
    /// conflicts – an arithmetically growing schedule, matching cadical's
    /// `lim.rephase = conflicts + rephaseint * (rephased.total + 1)`.
    /// Default 1000 (cadical parity).
    pub rephase_interval: u64,
    /// Target phases (cadical `opts.target`): decision polarity falls back to
    /// the *target* phase (a snapshot of the largest conflict-free trail
    /// prefix, refreshed by every backtrack) instead of the saved
    /// phase. 0 = never, 1 = stable mode only, 2 = always. Default 1
    /// (cadical parity).
    pub target: u32,
    /// Enable the local-search "walk" rephase strategy (cadical `opts.walk`).
    /// Default true (cadical parity).
    pub walk: bool,
    /// Allow the walk strategy in focused mode too (cadical
    /// `opts.walknonstable`). Default true (cadical parity).
    pub walk_nonstable: bool,
    /// Relative walk effort in per-mille of the search ticks accumulated since
    /// the last walk (cadical `opts.walkeffort`, default 80 = 8%).
    pub walk_effort: u64,
    /// Pre-walk propagation warmup (cadical `opts.warmup`, default ON there):
    /// before a walk round, decide+propagate to a full assignment IGNORING
    /// conflicts and seed the walk from it — ProbSAT cannot discover
    /// propagation chains, so this gives local search a consistent start.
    /// Default OFF in OxiZ pending measurement (see the walk study).
    pub walk_warmup: bool,
    /// Whether restarts reuse the decision trail prefix (Heule/cadical
    /// reuse-trail) instead of backtracking to the root. Default true.
    pub reuse_trail: bool,
    /// Run failed-literal probing as the first step of inprocessing. Default
    /// true; can be disabled to exercise the other inprocessing passes
    /// (pure-literal / subsumption / strengthening) in isolation.
    pub enable_failed_literal_probing: bool,
    /// Run failed-literal probing with on-the-fly hyper-binary resolution as
    /// part of inprocessing. Default true when inprocessing is on.
    pub enable_hyper_binary_probing: bool,
    /// Try CaDiCaL-style "lucky" pre-solving phase guesses before search
    /// (uniform all-false / all-true, ordered-with-flip, positive/negative
    /// Horn). Default **true**, matching CaDiCaL's `opts.lucky = 1`: the
    /// strategies are soundness-preserving – a doomed guess performs at most a
    /// pure `O(|literals|)` scan or a single-literal-at-a-time probe that
    /// backtracks to the root on failure, so it never perturbs the search
    /// state. Set `false` to disable (e.g. to isolate search-only behaviour).
    pub enable_lucky: bool,
    /// Optional external branching heuristic. When `Some`, called before built-in
    /// VSIDS/LRB/CHB; returning `None` from the heuristic falls back to built-in.
    /// Default: `None` (pure built-in strategy).
    pub external_branching: Option<BoxedBranchingHeuristic>,
}

impl core::fmt::Debug for SolverConfig {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SolverConfig")
            .field("restart_interval", &self.restart_interval)
            .field("restart_multiplier", &self.restart_multiplier)
            .field("clause_deletion_threshold", &self.clause_deletion_threshold)
            .field("var_decay", &self.var_decay)
            .field("clause_decay", &self.clause_decay)
            .field("random_polarity_prob", &self.random_polarity_prob)
            .field("restart_strategy", &self.restart_strategy)
            .field("enable_lazy_hyper_binary", &self.enable_lazy_hyper_binary)
            .field("use_chb_branching", &self.use_chb_branching)
            .field("use_lrb_branching", &self.use_lrb_branching)
            .field("rephase", &self.rephase)
            .field("rephase_interval", &self.rephase_interval)
            .field("enable_shrink", &self.enable_shrink)
            .field("target", &self.target)
            .field("walk", &self.walk)
            .field("enable_inprocessing", &self.enable_inprocessing)
            .field("inprocessing_interval", &self.inprocessing_interval)
            .field(
                "enable_chronological_backtrack",
                &self.enable_chronological_backtrack,
            )
            .field(
                "chrono_backtrack_threshold",
                &self.chrono_backtrack_threshold,
            )
            .field(
                "external_branching",
                &self
                    .external_branching
                    .as_ref()
                    .map(|_| "<BranchingHeuristic>"),
            )
            .finish()
    }
}

/// Restart strategy
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RestartStrategy {
    /// Luby sequence restarts
    Luby,
    /// Geometric restarts
    Geometric,
    /// Glucose-style dynamic restarts based on LBD
    Glucose,
    /// Local restarts based on LBD trail
    LocalLbd,
}

/// Which rephase strategy produced the current phase array (cadical's
/// `rephased` character). Tracked so [`Solver::update_target_and_best`] can
/// tell whether the recorded best phase predates the rephase that is about to
/// be overwritten (a `best` rephase re-arms `best_assigned` so a fresh best can
/// be found after it).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RephaseKind {
    /// All phases set to the initial phase (`O`).
    Original,
    /// All phases set to the inverted initial phase (`I`).
    Inverted,
    /// Every phase flipped in place (`F`).
    Flipping,
    /// All phases re-randomized (`#`).
    Random,
    /// Saved phases overwritten from the best-phase array (`B`).
    Best,
    /// Local search over the saved phases (`W`).
    Walk,
}

impl Default for SolverConfig {
    fn default() -> Self {
        Self {
            restart_interval: 100,
            restart_multiplier: 1.5,
            clause_deletion_threshold: 10000,
            var_decay: 0.95,
            clause_decay: 0.999,
            random_polarity_prob: 0.02,
            random_polarity_prob_stable: None,
            restart_strategy: RestartStrategy::Luby,
            // Off by default: the lazy hyper-binary derivation in
            // `check_hyper_binary_resolution` is not currently sound.  Its learned
            // binaries go straight into the binary implication graph, where they
            // both propagate and act as conflict reasons, so an unimplied one
            // produces a wrong top-level UNSAT on satisfiable input (QF_UF
            // quasigroup `iso_brn*`: enabling it flips `sat` to `unsat`, and a
            // wrong UNSAT can only come from a clause the formula does not
            // entail).  Re-enable once the derivation is proven and tested.
            enable_lazy_hyper_binary: false,
            use_chb_branching: false,
            use_lrb_branching: false,
            enable_inprocessing: false,
            enable_equiv_substitution: false,
            enable_gate_congruence: true,
            enable_bve: false,
            enable_sbva: false,
            inprocessing_interval: 5000,
            elim_interval: 2000,
            enable_chronological_backtrack: true,
            chrono_always: std::env::var("OXIZ_CHRONO_ALWAYS").is_ok_and(|v| v == "1"),
            chrono_reuse: std::env::var("OXIZ_CHRONO_REUSE").is_ok_and(|v| v == "1"),
            chrono_reuse_after: 0,
            chrono_backtrack_threshold: 100,
            luby_cap: 64,
            enable_stabilize: true,
            enable_shrink: true,
            presearch_collapse: false,
            stabilize_base: 5000,
            focused_luby_cap: 16,
            use_vmtf: true,
            focused_vmtf: true,
            rephase: 1,
            rephase_interval: 1000,
            target: 1,
            walk: true,
            walk_nonstable: true,
            walk_effort: 80,
            walk_warmup: std::env::var("OXIZ_WARMUP").is_ok_and(|v| v != "0"),
            reuse_trail: true,
            // Off by default: BOTH probing passes previously had a proven
            // false-UNSAT on satisfiable input (`circuit_48in64out_with_700gates…cnf`,
            // CaDiCaL model verified): running *either* pass alone (everything
            // else disabled) answered `unsat` on that SATISFIABLE file.  Root
            // cause identified and fixed (2026-08 SAT soundness sweep): the
            // probes propagate through the corrupted second-watch placement
            // `learn_clause` used to leave in stored clauses (see the
            // watch-position fix in `learn.rs` / the regression tests in
            // `tests/watch_position_soundness.rs`); with that fixed, probing
            // solves that same file `sat` in seconds.  They stay gated behind
            // `enable_inprocessing` (still off in every preset) until the
            // separate `inprocess()` watch-rebuild unsoundness is fixed.  The
            // sound pre-search combination is lucky phases + inprocessing
            // (subsumption round + vivification), which solves
            // `mrpp_4x4#12_12` in ~5 ms / 335 conflicts.
            enable_failed_literal_probing: false,
            enable_hyper_binary_probing: false,
            enable_lucky: true,
            external_branching: None,
        }
    }
}

/// Statistics for the solver
#[derive(Debug, Default, Clone)]
pub struct SolverStats {
    /// Number of decisions made
    pub decisions: u64,
    /// Number of propagations
    pub propagations: u64,
    /// Number of conflicts
    pub conflicts: u64,
    /// Number of restarts
    pub restarts: u64,
    /// Number of learned clauses
    pub learned_clauses: u64,
    /// Number of deleted clauses
    pub deleted_clauses: u64,
    /// Number of binary clauses learned
    pub binary_clauses: u64,
    /// Number of unit clauses learned
    pub unit_clauses: u64,
    /// Number of variables eliminated by equivalent-literal substitution.
    pub substitutions: u64,
    /// Number of variables eliminated by bounded variable elimination (BVE).
    pub bve_eliminated: u64,
    /// Number of clauses removed by forward subsumption.
    pub subsumed_removed: u64,
    /// Number of literals removed by BIG-based self-subsumption.
    pub self_subsumed: u64,
    /// Total LBD of learned clauses
    pub total_lbd: u64,
    /// Number of clause minimizations
    pub minimizations: u64,
    /// Literals removed by minimization
    pub literals_removed: u64,
    /// Number of chronological backtracks
    pub chrono_backtracks: u64,
    /// Number of non-chronological backtracks
    pub non_chrono_backtracks: u64,
    /// Clause-arena compactions performed (arena garbage collection;
    /// see `Solver::compact_clause_arena_if_due`).
    pub arena_compactions: u64,
    /// Number of CaDiCaL-style "lucky" pre-solving attempts (see `lucky_phases`).
    pub lucky_tried: u64,
    /// Number of "lucky" attempts that produced a model without search.
    pub lucky_succeeded: u64,
    /// Conflicts accumulated while in stable mode (cadical
    /// `stats.stabconflicts`); drives the stable-only rephase schedule
    /// (`rephase == 2`).
    pub stable_conflicts: u64,
    /// Restarts that fired while in stable mode (cadical
    /// `stats.restartstable`) – the reluctant-doubling restarts.
    pub restarts_stable: u64,
    /// Restarts that reused a non-empty decision prefix (cadical
    /// `stats.reused`).
    pub reused_trails: u64,
    /// Total decision levels kept by reuse-trail restarts (cadical
    /// `stats.reusedlevels`).
    pub reused_levels: u64,
    /// Learned literals removed by block-UIP clause shrinking (cadical
    /// `stats.shrunken`).
    pub shrunken: u64,
    /// Learned literals removed by the minimizer fallback inside shrinking
    /// (cadical `stats.minishrunken`).
    pub minishrunken: u64,
    /// Rephasing counters (cadical `stats.rephased`).
    pub rephased: RephaseCounters,
    /// Local-search walk counters (cadical `stats.walk`).
    pub walk: WalkCounters,
}

/// Per-strategy rephase counters (cadical `stats.rephased`).
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct RephaseCounters {
    /// Total rephases performed.
    pub total: u64,
    /// `original` strateg ies: all phases set to the initial phase.
    pub original: u64,
    /// `inverted` strategies: all phases set to the inverted initial phase.
    pub inverted: u64,
    /// `flipping` strategies: every phase flipped in place.
    pub flipped: u64,
    /// `random` strategies: all phases re-randomized.
    pub random: u64,
    /// `best` strategies: saved phases overwritten by the best-phase array.
    pub best: u64,
    /// `walk` strategies: ProbSAT local search over the saved phases.
    pub walk: u64,
}

/// Local-search walk counters (cadical `stats.walk`).
#[derive(Debug, Default, Clone, Copy)]
pub struct WalkCounters {
    /// Number of walks performed.
    pub count: u64,
    /// Number of variable flips across all walks.
    pub flips: u64,
    /// Best (smallest) number of broken clauses ever reached (global).
    pub minimum: u64,
    /// Broken-clause counter accumulated per flip (cadical
    /// `stats.walk.broken`); proxy for flip quality.
    pub broken: u64,
    /// Ticks consumed by walks.
    pub ticks: u64,
    /// Pre-walk propagation warmups performed (cadical `stats.warmup.count`).
    pub warmups: u64,
    /// Conflicts ignored during warmup passes (cadical
    /// `stats.warmup.conflicts`).
    pub warmup_conflicts: u64,
}

impl SolverStats {
    /// Get average LBD of learned clauses
    #[must_use]
    pub fn avg_lbd(&self) -> f64 {
        if self.learned_clauses == 0 {
            0.0
        } else {
            self.total_lbd as f64 / self.learned_clauses as f64
        }
    }

    /// Get average decisions per conflict
    #[must_use]
    pub fn avg_decisions_per_conflict(&self) -> f64 {
        if self.conflicts == 0 {
            0.0
        } else {
            self.decisions as f64 / self.conflicts as f64
        }
    }

    /// Get propagations per conflict
    #[must_use]
    pub fn propagations_per_conflict(&self) -> f64 {
        if self.conflicts == 0 {
            0.0
        } else {
            self.propagations as f64 / self.conflicts as f64
        }
    }

    /// Get clause deletion ratio
    #[must_use]
    pub fn deletion_ratio(&self) -> f64 {
        if self.learned_clauses == 0 {
            0.0
        } else {
            self.deleted_clauses as f64 / self.learned_clauses as f64
        }
    }

    /// Get chronological backtrack ratio
    #[must_use]
    pub fn chrono_backtrack_ratio(&self) -> f64 {
        let total = self.chrono_backtracks + self.non_chrono_backtracks;
        if total == 0 {
            0.0
        } else {
            self.chrono_backtracks as f64 / total as f64
        }
    }

    /// Display formatted statistics
    pub fn display(&self) {
        println!("========== Solver Statistics ==========");
        println!("Decisions:              {:>12}", self.decisions);
        println!("Propagations:           {:>12}", self.propagations);
        println!("Conflicts:              {:>12}", self.conflicts);
        println!("Restarts:               {:>12}", self.restarts);
        println!("Learned clauses:        {:>12}", self.learned_clauses);
        println!("  - Unit clauses:       {:>12}", self.unit_clauses);
        println!("  - Binary clauses:     {:>12}", self.binary_clauses);
        println!("Deleted clauses:        {:>12}", self.deleted_clauses);
        println!("Minimizations:          {:>12}", self.minimizations);
        println!("Literals removed:       {:>12}", self.literals_removed);
        println!("Chrono backtracks:      {:>12}", self.chrono_backtracks);
        println!("Non-chrono backtracks:  {:>12}", self.non_chrono_backtracks);
        println!("Arena compactions:      {:>12}", self.arena_compactions);
        println!("Rephases:               {:>12}", self.rephased.total);
        println!(
            "  original/inverted:    {:>5}/{:<8}",
            self.rephased.original, self.rephased.inverted
        );
        println!(
            "  flipping/random:      {:>5}/{:<8}",
            self.rephased.flipped, self.rephased.random
        );
        println!(
            "  best/walk:            {:>5}/{:<8}",
            self.rephased.best, self.rephased.walk
        );
        println!("Walks:                  {:>12}", self.walk.count);
        println!("Walk flips:             {:>12}", self.walk.flips);
        println!("---------------------------------------");
        println!("Avg LBD:                {:>12.2}", self.avg_lbd());
        println!(
            "Avg decisions/conflict: {:>12.2}",
            self.avg_decisions_per_conflict()
        );
        println!(
            "Propagations/conflict:  {:>12.2}",
            self.propagations_per_conflict()
        );
        println!(
            "Deletion ratio:         {:>12.2}%",
            self.deletion_ratio() * 100.0
        );
        println!(
            "Chrono backtrack ratio: {:>12.2}%",
            self.chrono_backtrack_ratio() * 100.0
        );
        println!("=======================================");
    }
}

/// Search-state memory composition (see [`Solver::memory_composition`]).
#[derive(Debug, Clone, Copy)]
pub struct MemoryComposition {
    /// Clause-arena live region (bytes).
    pub arena_used_bytes: usize,
    /// Clause-arena allocation capacity (bytes).
    pub arena_capacity_bytes: usize,
    /// Arena bytes in deleted-but-uncompacted slots.
    pub arena_wasted_bytes: usize,
    /// The dense id→ref table (4 bytes per clause ever allocated).
    pub refs_bytes: usize,
    /// Watch-list live watcher bytes.
    pub watch_bytes: usize,
    /// Watch-list capacity (doubling overshoot) bytes.
    pub watch_capacity_bytes: usize,
    /// Binary implication graph live edge bytes (8 per edge).
    pub big_edge_bytes: usize,
    /// Binary implication graph capacity bytes.
    pub big_capacity_bytes: usize,
    /// Arena compactions performed.
    pub arena_compactions: u64,
}

/// Soundness error from reintroducing a variable the inprocessing toolkit
/// (bounded variable elimination) already eliminated: its defining clauses
/// were resolved away, so there is no sound on-demand rewrite the way
/// equivalent-literal substitution has. ELS-substituted variables are
/// rewritten through the substitution map instead and never produce this.
///
/// Ported from v0.3.2's gatekeeper fix. main's BVE eliminates no variables
/// under its sound literal-count bound, so this is currently unreachable in
/// practice; it exists for correctness and to keep the contract honest.
#[derive(Debug, Clone)]
pub enum SolverError {
    /// A later `add_clause` or assumption named a BVE-eliminated variable.
    EliminatedVariableReintroduction {
        /// The variable a later clause or assumption tried to reintroduce.
        var: Var,
    },
}

/// Which branching strategy supplied the variable returned by the most
/// recent [`Solver::pick_branch_var`]. Recorded so a decision tracer (see
/// `Solver::trace_decision`, gated on `OXIZ_TRACE_DECISIONS`) can report the
/// source alongside each decision – the key diagnostic for whether any
/// theory-aware path is actually steering the search.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum BranchSource {
    /// `domain_priority` finite-domain table-index equalities.
    Domain,
    /// `config.external_branching` heuristic (the `branch_priority` queue).
    External,
    /// Learning-rate branching.
    Lrb,
    /// Conflict-history branching.
    Chb,
    /// VMTF move-to-front queue (cadical focused mode).
    Vmtf,
    /// VSIDS / EVSIDS heap (cadical stable mode).
    Vsids,
    /// Exhausted-heap linear scan fallback.
    Fallback,
}

/// CDCL SAT Solver
#[derive(Debug)]
pub struct Solver {
    /// Configuration
    pub(super) config: SolverConfig,
    /// A prior `add_clause`/assumption reintroduced a BVE-eliminated variable
    /// (see [`SolverError`]); once set, `solve*` answers `Unknown` rather
    /// than risk a wrong `Sat`/`Unsat`. Read via [`Solver::error`].
    pub(super) fatal_error: Option<SolverError>,
    /// Number of variables
    pub(super) num_vars: usize,
    /// Clause database
    pub(super) clauses: ClauseDatabase,
    /// Assignment trail
    pub(super) trail: Trail,
    /// Watch lists
    pub(super) watches: WatchLists,

    /// VSIDS branching heuristic
    pub(super) vsids: VSIDS,
    /// Prefer these variables before VSIDS (highest priority first). Cleared
    /// when empty; used for finite-domain table-index equalities.
    pub(super) domain_priority: Vec<Var>,
    /// VMTF move-to-front decision queue (cadical focused-mode branching).
    pub(super) vmtf: VMTF,
    /// CHB branching heuristic
    pub(super) chb: CHB,
    /// LRB branching heuristic
    pub(super) lrb: LRB,
    /// Statistics
    pub(super) stats: SolverStats,
    /// Learnt clause for conflict analysis
    pub(super) learnt: SmallVec<[Lit; 32]>,
    /// Seen flags for conflict analysis
    pub(super) seen: Vec<bool>,
    /// Analyze stack
    pub(super) analyze_stack: Vec<Lit>,
    /// Current restart threshold
    pub(super) restart_threshold: u64,
    /// Assertions stack for incremental solving (number of original clauses)
    pub(super) assertion_levels: Vec<usize>,
    /// Set once `push()` is called.  Retracted clauses stay live in the database
    /// after `pop()` (watch lists are cleaned lazily), so the fully-falsified
    /// scan in `trail_falsifies_live_clause` cannot distinguish a genuinely
    /// broken trail from ordinary incremental bookkeeping; the check is disabled
    /// for the rest of this solver's life once incremental mode is entered.
    pub(super) ever_pushed: bool,
    /// Trail sizes at each assertion level (for proper pop backtracking)
    pub(super) assertion_trail_sizes: Vec<usize>,
    /// Clause IDs added at each assertion level (for proper pop)
    pub(super) assertion_clause_ids: Vec<Vec<ClauseId>>,
    /// Model (if sat)
    pub(super) model: Vec<LBool>,
    /// Whether formula is trivially unsatisfiable
    pub(super) trivially_unsat: bool,
    /// Optional per-call propagation step limit for preprocessing passes
    /// (lucky/probing/vivify). When set, `propagate` stops and sets
    /// `propagate_aborted` once the limit is reached, so a single doomed
    /// cascade can't run unbounded (it was a ~7s slowdown on Urquhart). `None`
    /// (the default, used by the real search) means no limit.
    pub(super) propagate_step_limit: Option<u64>,
    /// Set by `propagate` when it bailed early due to `propagate_step_limit`.
    pub(super) propagate_aborted: bool,
    /// Which branching strategy supplied the last decision variable. See
    /// [`BranchSource`]; set inside [`Solver::pick_branch_var`], read by the
    /// optional decision tracer.
    pub(super) last_branch_source: BranchSource,
    /// Phase saving: last polarity assigned to each variable
    /// (cadical `phases.saved`).
    pub(super) phase: Vec<bool>,
    /// Theory-supplied deterministic initial phases.  Unlike ordinary saved
    /// phases these are not randomized or globally inverted; they are used for
    /// atoms where a theory can provide a mutually coherent candidate model
    /// (for example, an acyclic orientation of arithmetic disequalities).
    /// They remain decision preferences only: clauses may propagate the
    /// opposite value and conflict analysis remains unchanged.  Takes
    /// precedence over target and saved phases exactly like cadical's
    /// `phases.forced` (see `decision_polarity`).
    pub(super) deterministic_phase: Vec<Option<bool>>,
    /// Best partial assignment ever seen (cadical `phases.best`): the saved
    /// phases copied at the moment the trail's largest conflict-free prefix
    /// (`no_conflict_until`) exceeded every earlier one (`best_assigned`).
    /// Restored by the `best` rephase strategy.
    pub(super) best_phase: Vec<bool>,
    /// Target phases (cadical `phases.target`): like `best_phase` but
    /// re-established from scratch after every rephase – the phase snapshot
    /// the decision heuristic prefers while in stable mode
    /// (cadical `decide_phase(idx, target)`).
    pub(super) target_phase: Vec<bool>,
    /// Size of the conflict-free trail prefix recorded in `target_phase`
    /// (cadical `target_assigned`; reset to 0 after each rephase).
    pub(super) target_assigned: usize,
    /// Size of the conflict-free trail prefix recorded in `best_phase`
    /// (cadical `best_assigned`; reset to 0 when the last rephase was a
    /// `best` rephase and a conflict has happened since).
    pub(super) best_assigned: usize,
    /// Largest trail prefix that propagated without conflict
    /// (cadical `no_conflict_until`): updated by `propagate` – set to the full
    /// trail on a clean fixpoint, to the prefix before the current decision
    /// level on a conflict – and clamped by every backtrack. Read by
    /// [`Solver::update_target_and_best`].
    pub(super) no_conflict_until: usize,
    /// Type of the most recent rephase (cadical `rephased` char). Cleared by
    /// `update_target_and_best` once a conflict has occurred since it was
    /// set, which is also what re-arms target/best recording.
    pub(super) rephased: Option<RephaseKind>,
    /// Conflict count at the most recent rephase (cadical
    /// `last.rephase.conflicts`).
    pub(super) last_rephase_conflicts: u64,
    /// Next conflict count at which to rephase (cadical `lim.rephase`).
    pub(super) lim_rephase: u64,
    /// Per-mode rephase round counters `[focused, stable]` (cadical
    /// `lim.rephased[stable]`); reset at every solve start like cadical's
    /// `init_search_limits`.
    pub(super) rephase_rounds: [u64; 2],
    /// Search ticks at the last walk (cadical `last.walk.ticks`); the walk
    /// effort budget is a per-mille fraction of the ticks accumulated since.
    pub(super) last_walk_ticks: u64,
    /// Luby sequence index for restarts
    pub(super) luby_index: u64,
    /// cadical-style stable/focused mode flag. Focused (false) = frequent
    /// restarts (aggressive search); stable (true) = rare restarts + rephase
    /// (deep exploration). Alternated on a growing schedule.
    pub(super) stable: bool,
    /// Stabilization phase counter (drives the quadratic switch-interval
    /// growth).
    pub(super) stabphases: u64,
    /// Conflict count at which to next switch stable/focused mode.
    ///
    /// Legacy: the tick-based schedule (`lim_stabilize`) drives the actual
    /// transitions; retained for inspection but not read by the search.
    #[allow(dead_code)]
    pub(super) next_stabilize: u64,
    /// Per-mode glue averages (current/saved), swapped on stable/focused
    /// transitions (cadical `swap_averages`).
    pub(super) glue_current: GlueAverages,
    pub(super) glue_saved: GlueAverages,
    /// Knuth reluctant-doubling (Luby) restart trigger for stable mode.
    pub(super) reluctant: Reluctant,
    /// Per-mode tick (propagation) accumulators (cadical `stats.ticks.search`).
    pub(super) ticks_focused: u64,
    pub(super) ticks_stable: u64,
    /// cadical `lim.restart`: next conflict count at which to check the
    /// focused-mode Glucose restart condition.
    pub(super) lim_restart: u64,
    /// cadical `lim.stabilize` expressed in ticks of the upcoming mode.
    pub(super) lim_stabilize: u64,
    /// Level marks for LBD computation
    pub(super) level_marks: Vec<u32>,
    /// Current mark counter for LBD computation
    pub(super) lbd_mark: u32,
    /// Learned clause IDs for deletion
    pub(super) learned_clause_ids: Vec<ClauseId>,
    /// Number of conflicts since last clause deletion
    pub(super) conflicts_since_deletion: u64,
    /// Level-0 trail length at the last [`Solver::sweep_root_fixed_clauses`]
    /// (cadical `last.collect.fixed`): the sweep only runs when new root
    /// facts appeared since the previous one.
    pub(super) last_sweep_fixed: usize,
    /// cadical-reduce port (`OXIZ_CADICAL_REDUCE`, study in
    /// `docs/studies/`): conflict count at which the next cadical-style
    /// reduction fires (cadical `lim.reduce`; first at `reduceinit` = 300).
    pub(super) cadical_reduce_next: u64,
    /// Completed cadical-style reductions (cadical `stats.reductions`;
    /// feeds the growing `delta = reduceint * sqrt(conflicts)` schedule).
    pub(super) cadical_reductions: u64,
    /// cadical `Clause::used`: recency-of-use stamp per learned clause id
    /// (`max_used` = 31 set on every analysis bump, decremented once per
    /// reduction round; glue-tiered retention reads it). Indexed by
    /// `ClauseId::index()`.
    pub(super) cadical_used: Vec<u8>,
    /// Faithful-stabilize port (`OXIZ_STAB_FAITHFUL`, study in
    /// `docs/studies/`): cadical `inc.stabilize` – the tick length of the
    /// first focused phase, measured at its end; 0 until then. Later phase
    /// lengths are `stab_inc x stabphases^2`.
    pub(super) stab_inc: u64,
    /// Tick counter of the current mode captured at its last stabilization
    /// switch (cadical `last.stabilize.ticks`, taken per mode).
    pub(super) stab_last_ticks: u64,
    /// Scratch for the shuffled-phase-length null (`OXIZ_STAB_NULL`): the
    /// not-yet-consumed quadratic sequence values.
    pub(super) stab_null_pending: Vec<u64>,
    /// PRNG state (xorshift64)
    pub(super) rng_state: u64,
    /// Seed [`Self::rng_state`] was initialized from (set via
    /// [`Solver::set_rng_seed`]); `reset()` restores the same stream so
    /// per-seed trajectories stay reproducible across repeated solves.
    pub(super) rng_seed: u64,
    /// For Glucose-style restarts: average LBD of recent conflicts
    pub(super) recent_lbd_sum: u64,
    /// Number of conflicts contributing to recent_lbd_sum
    pub(super) recent_lbd_count: u64,
    /// Fast EMA of learned-clause LBD (short window) for Glucose restarts.
    /// Restart when this exceeds the slow EMA – clause quality is degrading.
    pub(super) lbd_ema_fast: f64,
    /// Slow EMA of learned-clause LBD (long window) for Glucose restarts.
    pub(super) lbd_ema_slow: f64,
    /// Binary implication graph for fast binary clause propagation
    pub(super) binary_graph: BinaryImplicationGraph,
    /// Global average LBD for local restarts
    pub(super) global_lbd_sum: u64,
    /// Number of conflicts contributing to global LBD
    pub(super) global_lbd_count: u64,
    /// Conflicts since last local restart
    pub(super) conflicts_since_local_restart: u64,
    /// Conflicts since last inprocessing
    pub(super) conflicts_since_inprocessing: u64,
    /// A real (non no-op) theory callback is attached to the running search.
    /// Set for the duration of [`Solver::solve_with_theory`] when the
    /// callback reports [`TheoryCallback::is_real_theory`]; gates the
    /// pure-literal pass of [`Solver::inprocess`] (see the trait method's
    /// soundness note).
    pub(super) real_theory_attached: bool,
    /// Freeze set (cdclt-gates-audit enabling slice): SAT variables whose
    /// assignments the theory callback observes.  Destructive preprocessing
    /// (BVE elimination, ELS folding, pure-literal elimination) skips frozen
    /// variables, which lets those passes run under a REAL theory when the
    /// caller has frozen the theory-mapped set — the transforms then only
    /// touch Boolean-structure (Tseitin/gate) variables the theory never
    /// sees.  Frozen forever once frozen: the set only ever shrinks what the
    /// passes may do, so retaining entries past a hypothetical un-mapping is
    /// the conservative direction.
    pub(super) frozen_vars: rustc_hash::FxHashSet<Var>,
    /// Whether [`Solver::freeze_theory_vars`] has been called — the
    /// precondition that relaxes the `real_theory_attached` gates.
    pub(super) theory_vars_frozen: bool,
    /// Chronological backtracking helper
    pub(super) chrono_backtrack: ChronoBacktrack,
    /// Clause activity bump increment (for MapleSAT-style clause bumping)
    pub(super) clause_bump_increment: f64,
    /// Memory optimizer with size-class pools for clause allocation
    pub(super) memory_optimizer: MemoryOptimizer,
    /// Model-reconstruction stack for pure literals eliminated during
    /// inprocessing. Pure-literal elimination deletes clauses that are only
    /// satisfiable *if* the pure literal is fixed to its polarity; the search
    /// itself may assign the variable the opposite phase, so each recorded
    /// literal is forced to `true` in the reconstructed model (see
    /// [`Solver::save_model`]). At most one polarity per variable is recorded.
    pub(super) pure_literal_reconstruction: Vec<Lit>,
    /// One-shot latch: once equivalent-literal substitution has rewritten the
    /// clause database we must not run it again (a second pass would operate on
    /// already-substituted clauses and, for incremental callers, on top of
    /// assumptions/blocking clauses expressed in the original variable space).
    pub(super) did_equiv_subst: bool,
    /// Whether `equiv_substitution` has been identity-initialized (one-time;
    /// subsequent substitution rounds compose onto it).
    pub(super) equiv_subst_inited: bool,
    /// Model-reconstruction map for equivalent-literal substitution
    /// (`equiv.rs`): `equiv_substitution[v]` is the representative literal
    /// whose value variable `v` should inherit in the model. For a variable
    /// that was *not* eliminated this is `Lit::pos(v)` (identity). For an
    /// eliminated variable it is a literal of a different variable.
    pub(super) equiv_substitution: Vec<Lit>,
    /// Model-reconstruction data for BVE-eliminated variables. Indexed by
    /// variable; `bve_def[v]` holds the non-`v` literals of every clause that
    /// contained `v` *positively* at elimination time. At model-extension time
    /// `v` is set true iff all of those clauses are falsified by the current
    /// model (else false) – see [`Solver::save_model`].
    pub(super) bve_def: Vec<Vec<SmallVec<[Lit; 4]>>>,
    /// Elimination order of BVE-eliminated variables (reconstruction runs in
    /// reverse, so a variable eliminated later – which may appear in an earlier
    /// variable's recorded clauses – is assigned first).
    pub(super) bve_order: Vec<Var>,
    /// Inprocessing-elimination state (cadical `elim.cpp` port, see
    /// `solver/eliminate.rs`). `elim_mark[i]`: variable `i` occurred in a
    /// removed or shrunken original clause since the last elimination phase
    /// and is scheduled as a candidate (cadical `flags.elim`).
    pub(super) elim_mark: Vec<bool>,
    /// Number of set bits in `elim_mark` (cadical `stats.mark.elim`).
    pub(super) elim_mark_count: usize,
    /// Growing elimination bound (cadical `lim.elimbound`): extra resolvents
    /// allowed beyond the removed-clause count. 0 → 1 → 2 → 4 → … → 16.
    pub(super) elim_bound: i64,
    /// Elimination phases run so far (cadical `stats.elimphases`).
    pub(super) elim_phases: u64,
    /// Conflict threshold for the next elimination phase (cadical `lim.elim`).
    pub(super) lim_elim: u64,
    /// Level-0 trail length at the last elimination phase (cadical
    /// `last.elim.fixed`): new units re-arm elimination.
    pub(super) last_elim_fixed: usize,
    /// Set when the elimination bound saturated and a phase completed with
    /// nothing eliminated: stop scheduling phases.
    pub(super) elim_finished: bool,
    /// Cumulative resolution steps consumed by elimination rounds (cadical
    /// `stats.elimres`), driving the per-round budget.
    pub(super) elim_resolutions_total: u64,
    /// Variables eliminated by the most recent elimination phase; drives the
    /// pre-search fixpoint loop's productivity gate.
    pub(super) last_elim_eliminated: u64,
    /// Variables eliminated by the inprocessing eliminator (`eliminate.rs`).
    /// Distinct from `bve_def` non-emptiness: a variable can be eliminated
    /// with an empty positive-side snapshot (all its positive clauses were
    /// retired as satisfied before elimination), and it must still count as
    /// eliminated for decision/propagation purposes.
    pub(super) elim_var_flag: Vec<bool>,
    /// Per-clause transred metadata, indexed by dense `ClauseId` (ids are
    /// never reused, so these vectors cannot go stale):
    /// `clause_transred_checked[i]` – binary already examined by a
    /// transitive-reduction round (cadical `Clause::transred`); reset
    /// wholesale once every candidate has been checked.
    /// `clause_hyper[i]` – produced by hyper-binary resolution (cadical
    /// `Clause::hyper`); transred skips these as candidates (they arrive in
    /// bulk, are mostly reduced away, and were non-transitive at creation).
    pub(super) clause_transred_checked: Vec<bool>,
    pub(super) clause_hyper: Vec<bool>,
    /// `propfixed` memoization for failed-literal probing (cadical
    /// `propfixed`): per-literal count of level-0 assignments at the moment
    /// that literal last propagated without conflict. Re-probing is skipped
    /// while no new level-0 facts have appeared. -1 = never probed.
    pub(super) probe_propfixed: Vec<i64>,
    /// Probe rounds completed (cadical `stats.probingphases`), driving the
    /// `25 × interval × log10(rounds+9)` re-arm schedule.
    pub(super) elim_probes_done: u64,
    /// Conflict threshold for the next probe round (cadical `lim.inprobe`).
    pub(super) lim_inprobe: u64,
    /// Whether `lim_inprobe` has been derived from the input formula size
    /// (once per solver instance; cadical keeps its initial limit on
    /// incremental solves).
    pub(super) lim_inprobe_inited: bool,
    /// Level-0 trail size after the last probe round (re-arm evidence).
    pub(super) last_probe_units: usize,
    /// True while a `solve_with_assumptions` call is in flight: destructive
    /// inprocessing (elimination) must not fold variables out of the search
    /// then (cadical freezes assumed variables instead).
    pub(super) assumptions_active: bool,
    pub(super) interrupt: Option<Arc<AtomicBool>>,
    /// Optional conflict budget. When `Some(n)`, the search loop returns
    /// [`SolverResult::Unknown`] once `n` conflicts have been reached instead of
    /// running unbounded. `None` (the default) means no conflict limit. This is
    /// the resource budget consulted by the CDCL loop and drives, e.g.,
    /// `oxiz-cli --timeout`-style bounded solving.
    pub(super) max_conflicts: Option<u64>,
    /// Proof dispatcher (`class Proof`). When `Some`, every proof event the
    /// CDCL loop / inprocessing emits (learned/original/deleted clause, empty
    /// clause, in-place strengthen/flush) is fanned out to the attached
    /// tracers ([`crate::proof::DratTracer`] and/or [`crate::proof::LratTracer`]).
    /// `None` (the default) means no proof is produced and every proof hook is a
    /// no-op, so proof logging costs nothing when unused.
    pub(super) proof: Option<crate::proof::Proof>,
    /// `true` once an LRAT tracer (or any antecedent-requiring tracer) is
    /// connected. Drives clause-id bookkeeping (`clause_lrat_id`,
    /// `unit_clauses_idx`) and RUP-chain assembly in conflict analysis. DRAT-only
    /// proofs leave this `false` – DRAT needs neither ids nor chains.
    pub(super) lrat: bool,
    /// Level-0 units forced by `add_clause`'s effective-unit path during
    /// parsing, waiting for their LRAT flush at solve entry (emitting them
    /// mid-parse would allocate derived ids inside the original-clause
    /// prefix and desynchronize every later original's id — see the
    /// ForceUnitAtLevelZero sites). Each entry is `(forced literal, forcing
    /// clause)`.
    pub(super) pending_parse_unit_flushes: Vec<(crate::literal::Lit, ClauseId)>,
    /// Lazy explanations for theory-propagated assignments: for each variable
    /// assigned via [`Solver::assign_theory_propagation`], the antecedent
    /// literal tail a materialized reason clause would have carried (every
    /// literal FALSE on the trail at assignment time). Consulted by conflict
    /// analysis and clause minimization to resolve *through* a theory
    /// propagation without materializing its explanation as a clause – z3's
    /// `th_propagate`/`explain` design. Only populated while
    /// [`Solver::theory_lazy_reasons_enabled`] (a proof run materializes
    /// reason clauses instead, because the proof needs them in the database).
    ///
    /// Entries are written immediately before the trail assignment and are
    /// therefore exactly as current as the assignment they justify; an entry
    /// whose variable has been unassigned is dead (nothing consults it, since
    /// `Reason::Theory` is only observable while assigned) and is simply
    /// overwritten by the next theory propagation of that variable. Bounded by
    /// the variable count.
    pub(super) theory_prop_reasons: rustc_hash::FxHashMap<Var, SmallVec<[Lit; 8]>>,
    /// Materialized theory-reason clauses so far this solve.  Drives the
    /// one-way lazy switch ([`Solver::theory_lazy_reasons_enabled`]).
    pub(super) theory_reason_clauses: u64,
    /// True once drat_emit_empty has concluded the proof with the empty
    /// clause. Guards against double finalization (a second UNSAT solve
    /// emitting a second empty clause). Ported from v0.3.2's
    /// `lrat_unsat_finalized`.
    pub(super) lrat_finalized: bool,
    /// Monotonic clause-id counter (`clause_id` in upstream). Original clauses
    /// draw ids `1..K` in file order; derived clauses draw the rest. Maintained
    /// only while a proof is active.
    pub(super) clause_id: i64,
    /// Per-stored-clause LRAT id, indexed by `ClauseId.index()` (`c->id` in
    /// upstream). `0` = unassigned/none. Grown only while `lrat` is on.
    pub(super) clause_lrat_id: Vec<i64>,
    /// Per-literal unit-clause id table (`unit_clauses_idx` in upstream),
    /// indexed by `Lit::index()` (`2·var + sign`). Holds the LRAT id of the
    /// (original or derived) unit clause fixing that literal true. Grown only
    /// while `lrat` is on.
    pub(super) unit_clauses_idx: Vec<i64>,
    /// LRAT RUP-chain scratch (`lrat_chain` in upstream): reason-clause ids
    /// collected during 1-UIP analysis, in trail-walk order, reversed at the
    /// end. Always present (empty when no proof).
    pub(super) lrat_chain: Vec<i64>,
    /// Unit-clause id chain collected during analysis (`unit_chain`):
    /// level-0 literals resolved out of reason clauses. Appended to
    /// `lrat_chain` before the final reversal.
    pub(super) unit_chain: Vec<i64>,
    /// Minimization chain scratch (`mini_chain` / `minimize_chain`): per
    /// Minimization chain scratch (`mini_chain` / `minimize_chain`): per
    /// minimized-away literal's reason sub-chain.
    pub(super) mini_chain: Vec<i64>,
    /// Level-0 literals marked `seen` during analysis, for cleanup
    /// (`unit_analyzed` in upstream).
    pub(super) unit_analyzed: Vec<i32>,
    /// Packed per-literal minimization flags (`Flags` in upstream), indexed by
    /// `Lit::index()`. Bit layout: [`MF_KEEP`]|[`MF_POISON`]|[`MF_REMOVABLE`]|
    /// [`MF_ADDED`]|[`MF_SEEN`]. Grown only while `lrat` is on.
    pub(super) lrat_flags: Vec<u8>,
    /// Literals marked during minimization, for flag cleanup (`minimized`).
    #[allow(dead_code)]
    pub(super) lrat_minimized: Vec<i32>,
    /// Per-decision-level count of literals marked `seen` during the current
    /// conflict analysis (cadical `Level::seen.count`). Feeds Don Knuth's
    /// `seen.count < 2` gate in clause minimization.
    pub(super) seen_level_count: Vec<u32>,
    /// Shrink-study accumulator (OXIZ_SHRINK_TRACE=1):
    /// (analyzes, learnt_lits, singleton_blocks, multi_blocks,
    ///  multi_block_lits, walk_success, walk_fail, fallback_saved).
    pub(super) shrink_trace: (u64, u64, u64, u64, u64, u64, u64, u64),
    /// Position-indexed summary of `MF_SHRINKABLE` for the shrink block
    /// scan (`solver/conflict.rs`): one [`ShrinkChunk`] per 64 trail
    /// positions, epoch-stamped per block so stale entries read as empty
    /// without a clearing pass. Capacity retained across conflicts.
    pub(super) shrink_summary: Vec<ShrinkChunk>,
    /// Monotone block counter stamping [`Solver::shrink_summary`].
    pub(super) shrink_epoch: u64,
    /// Epoch of the current block's active summary, or `None` while the
    /// block's scan is still probe-only (see `solver/conflict.rs`:
    /// activation is lazy, so dense blocks never pay for the summary).
    pub(super) shrink_active_epoch: Option<u64>,
    /// Shrink-study failure-reason counters (OXIZ_SHRINK_TRACE=1).
    pub(super) shrink_fail_low: u64,
    pub(super) shrink_fail_above: u64,
    pub(super) mini_reject_no_reason: u64,
    pub(super) mini_reject_poison: u64,
    pub(super) mini_reject_conflict_level: u64,
    pub(super) mini_reject_knuth: u64,
    pub(super) mini_reject_early_abort: u64,
    /// Per-decision-level smallest trail index among `seen` literals of the
    /// current analysis (cadical `Level::seen.trail`, reset to `u32::MAX`).
    /// Feeds the `v.trail <= l.seen.trail` early abort in minimization.
    pub(super) seen_level_trail: Vec<u32>,
    /// Decision levels that contributed a `seen` literal to the current
    /// analysis (cadical `levels`), so the two vectors above are reset in
    /// O(contributing levels), not O(num levels).
    pub(super) seen_levels: Vec<u32>,
    /// Whether the last rephase round was a debug no-op (see
    /// `OXIZ_REPHASE_OFF`): the post-rephase restart-consistency check must
    /// be skipped then, since no root backtrack ran.
    pub(super) rephase_skipped: bool,
    /// Glue of the last completed 1-UIP analysis **walk**: the number of
    /// distinct decision levels touched by the whole resolution walk
    /// (`seen_levels.len() - 1`, cadical `const int glue = levels.size() - 1`
    /// in `analyze`).  This is *not* the LBD of the stored clause: cadical
    /// feeds this walk statistic into the restart EMAs
    /// (`UPDATE_AVERAGE (averages.current.glue.fast/slow, glue)`), while the
    /// clause's own literal-level glue is a separate quantity there (tier
    /// assignment and `recompute_glue`).  The two differ wildly in
    /// distribution – the walk glue is larger and far noisier, which is
    /// exactly what makes the focused Glucose restart condition cross its
    /// margin early and often (cadical's first restart fires around conflict
    /// 73 on `stable-300`; feeding the smoother clause LBD instead starved
    /// our restarts until conflict ~1100 and locked the search into tall
    /// sparse-trail equilibria).
    pub(super) analysis_walk_glue: u32,
    /// Previous conflict's `analysis_walk_glue` – the lagged value the
    /// `OXIZ_GLUE_NULL` matched null feeds into the restart EMAs (same
    /// distribution, same timing, no current-conflict information).
    pub(super) analysis_walk_glue_prev: u32,
    /// The genuine conflict level of the analysis in progress (the highest
    /// decision level among the conflict clause's literals, which under
    /// chronological backtracking can sit below `decision_level()`).
    /// Minimization must reject literals at this level (cadical
    /// `v.level == level`), not at `decision_level()`.
    pub(super) current_conflict_level: u32,
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

impl Solver {
    /// Attach the two watchers of a clause whose stored literals are
    /// `l0`/`l1` (positions [0]/[1]): key `~l0` with blocker `l1`, and
    /// `~l1` with blocker `l0`.
    ///
    /// The watcher records the clause's **arena slot** alongside its id, so
    /// propagation can dereference the clause directly instead of walking the
    /// `refs[id]` table on every visit. Slots are append-only and never reused
    /// (`memory.rs`), so the slot stays bound to this exact clause for the
    /// watcher's lifetime; deletion keeps it readable under the deleted flag.
    ///
    /// `cid` must come straight from an `add_*` call – every other caller has
    /// only ever held ids of live clauses, so the `ref_of` lookup cannot miss;
    /// the debug assert documents that invariant, and release mode skips
    /// attachment for a missing ref (a watcher-less clause degrades search
    /// completeness for that clause but is not a soundness hazard: dropping a
    /// watch never fabricates implications).
    ///
    /// **Binary clauses (len == 2) are registered in the binary implication
    /// graph, not in the watch lists** (BIG-authoritative BCP, 2026-09):
    /// `propagate()` scans the BIG first, so a binary watch entry could never
    /// reach its arena load (measured; see
    /// `studies/2026-09-big-authoritative-bcp.md`) – the entry was pure scan
    /// volume. The phantom counter is bumped one per direction so the
    /// tick-driven schedules keep seeing the old watch-list sizes. Callers
    /// must NOT also add the BIG edges themselves (this is the single
    /// registration point; double edges are sound but double-scan and break
    /// tick parity).
    pub(super) fn attach_watchers(&mut self, cid: ClauseId, l0: Lit, l1: Lit) {
        let is_binary = self.clauses.get(cid).is_some_and(|c| c.lits.len() == 2);
        if is_binary {
            self.binary_graph.add(l0.negate(), l1, cid);
            self.binary_graph.add(l1.negate(), l0, cid);
            self.watches.phantom_bump(l0.negate());
            self.watches.phantom_bump(l1.negate());
            return;
        }
        let Some(r) = self.clauses.ref_of(cid) else {
            debug_assert!(
                false,
                "freshly added/known-live clause id without arena slot"
            );
            return;
        };
        self.watches.add(l0.negate(), Watcher::new(cid, r, l1));
        self.watches.add(l1.negate(), Watcher::new(cid, r, l0));
    }

    /// Create a new solver
    #[must_use]
    pub fn new() -> Self {
        Self::with_config(SolverConfig::default())
    }

    /// Create a new solver with configuration
    ///
    /// The `OXIZ_CHRONO_REUSE` / `OXIZ_CHRONO_ALWAYS` experiment overrides
    /// are re-applied here: presets hard-set both fields (`chrono_reuse:
    /// false` everywhere), which used to stomp the env knobs read in
    /// `SolverConfig::default` — the switches were dead for any
    /// preset-built solver (found while preparing the reuse re-study;
    /// `docs/studies/2026-08-chronoreusetrail-rejected.md` follow-up).
    #[must_use]
    pub fn with_config(config: SolverConfig) -> Self {
        let mut config = config;
        if let Ok(v) = std::env::var("OXIZ_CHRONO_REUSE") {
            config.chrono_reuse = v == "1";
        }
        if let Ok(v) = std::env::var("OXIZ_CHRONO_REUSE_AFTER")
            && let Ok(n) = v.parse::<u64>()
        {
            config.chrono_reuse_after = n;
            config.chrono_reuse = true;
        }
        if let Ok(v) = std::env::var("OXIZ_CHRONO_ALWAYS") {
            config.chrono_always = v == "1";
        }
        let chrono_enabled = config.enable_chronological_backtrack;
        let chrono_threshold = config.chrono_backtrack_threshold;
        let chrono_always = config.chrono_always;
        let stabilize_base = config.stabilize_base;
        let elim_interval = config.elim_interval;

        Self {
            restart_threshold: config.restart_interval,
            config,
            fatal_error: None,
            lrat_finalized: false,
            num_vars: 0,
            clauses: ClauseDatabase::new(),
            trail: Trail::new(0),
            watches: WatchLists::new(0),
            vsids: VSIDS::new(0),
            domain_priority: Vec::new(),
            vmtf: VMTF::new(0),
            chb: CHB::new(0),
            lrb: LRB::new(0),
            stats: SolverStats::default(),
            learnt: SmallVec::new(),
            seen: Vec::new(),
            analyze_stack: Vec::new(),
            assertion_levels: vec![0],
            ever_pushed: false,
            assertion_trail_sizes: vec![0],
            assertion_clause_ids: vec![Vec::new()],
            model: Vec::new(),
            trivially_unsat: false,
            propagate_step_limit: None,
            propagate_aborted: false,
            last_branch_source: BranchSource::Fallback,
            phase: Vec::new(),
            deterministic_phase: Vec::new(),
            best_phase: Vec::new(),
            target_phase: Vec::new(),
            target_assigned: 0,
            best_assigned: 0,
            no_conflict_until: 0,
            rephased: None,
            last_rephase_conflicts: 0,
            lim_rephase: 0,
            rephase_rounds: [0, 0],
            last_walk_ticks: 0,
            luby_index: 0,
            stable: false,
            stabphases: 0,
            next_stabilize: stabilize_base,
            glue_current: GlueAverages::new(),
            glue_saved: GlueAverages::new(),
            reluctant: Reluctant::default(),
            ticks_focused: 0,
            ticks_stable: 0,
            lim_restart: 0,
            lim_stabilize: 0,
            level_marks: Vec::new(),
            lbd_mark: 0,
            learned_clause_ids: Vec::new(),
            conflicts_since_deletion: 0,
            last_sweep_fixed: 0,
            cadical_reduce_next: 300,
            cadical_reductions: 0,
            cadical_used: Vec::new(),
            stab_inc: 0,
            stab_last_ticks: 0,
            stab_null_pending: Vec::new(),
            rng_state: 0x853c_49e6_748f_ea9b, // Random seed
            rng_seed: 0x853c_49e6_748f_ea9b,
            recent_lbd_sum: 0,
            recent_lbd_count: 0,
            lbd_ema_fast: 0.0,
            lbd_ema_slow: 0.0,
            binary_graph: BinaryImplicationGraph::new(0),
            global_lbd_sum: 0,
            global_lbd_count: 0,
            conflicts_since_local_restart: 0,
            conflicts_since_inprocessing: 0,
            real_theory_attached: false,
            frozen_vars: rustc_hash::FxHashSet::default(),
            theory_vars_frozen: false,
            chrono_backtrack: {
                let mut cb = ChronoBacktrack::new(chrono_enabled, chrono_threshold);
                cb.set_always(chrono_always);
                cb
            },
            clause_bump_increment: 1.0,
            memory_optimizer: MemoryOptimizer::new(),
            pure_literal_reconstruction: Vec::new(),
            equiv_substitution: Vec::new(),
            bve_def: Vec::new(),
            bve_order: Vec::new(),
            elim_mark: Vec::new(),
            elim_mark_count: 0,
            elim_bound: 0,
            elim_phases: 0,
            lim_elim: elim_interval,
            last_elim_fixed: 0,
            elim_finished: false,
            elim_resolutions_total: 0,
            last_elim_eliminated: 0,
            elim_var_flag: Vec::new(),
            clause_transred_checked: Vec::new(),
            clause_hyper: Vec::new(),
            probe_propfixed: Vec::new(),
            elim_probes_done: 0,
            lim_inprobe: INPROBE_INIT_LIMIT,
            lim_inprobe_inited: false,
            last_probe_units: 0,
            assumptions_active: false,
            did_equiv_subst: false,
            equiv_subst_inited: false,
            interrupt: None,
            max_conflicts: None,
            proof: None,
            lrat: false,
            pending_parse_unit_flushes: Vec::new(),
            theory_prop_reasons: rustc_hash::FxHashMap::default(),
            theory_reason_clauses: 0,
            clause_id: 0,
            clause_lrat_id: Vec::new(),
            unit_clauses_idx: Vec::new(),
            lrat_chain: Vec::new(),
            unit_chain: Vec::new(),
            mini_chain: Vec::new(),
            unit_analyzed: Vec::new(),
            lrat_flags: Vec::new(),
            lrat_minimized: Vec::new(),
            seen_level_count: Vec::new(),
            shrink_trace: (0, 0, 0, 0, 0, 0, 0, 0),
            shrink_summary: Vec::new(),
            shrink_epoch: 0,
            shrink_active_epoch: None,
            shrink_fail_low: 0,
            shrink_fail_above: 0,
            mini_reject_no_reason: 0,
            mini_reject_poison: 0,
            mini_reject_conflict_level: 0,
            mini_reject_knuth: 0,
            mini_reject_early_abort: 0,
            seen_level_trail: Vec::new(),
            seen_levels: Vec::new(),
            rephase_skipped: false,
            analysis_walk_glue: 0,
            analysis_walk_glue_prev: 0,
            current_conflict_level: 0,
        }
    }

    /// Enable DRAT proof logging to `path`.
    ///
    /// While enabled, the CDCL search emits a DRAT proof: one addition line per
    /// learned clause, one deletion line per clause removed by database
    /// reduction / subsumption / vivification / incremental forgetting, and the
    /// empty clause when unconditional UNSAT is derived. The resulting file can
    /// be checked by any DRAT proof checker. Enabling it does not change the
    /// search itself – only whether the trace is recorded.
    pub fn enable_drat_proof(&mut self, path: impl AsRef<std::path::Path>) -> std::io::Result<()> {
        self.connect_drat(path, false)
    }

    /// Disable all proof logging, flushing and closing every attached tracer.
    pub fn disable_proof(&mut self) {
        if let Some(mut proof) = self.proof.take() {
            proof.flush(false);
            proof.close(false);
        }
        self.lrat = false;
        self.lrat_finalized = true;
    }

    /// Back-compat alias for [`Solver::disable_proof`].
    pub fn disable_drat_proof(&mut self) {
        self.disable_proof();
    }

    /// Returns `true` when any proof logging is currently enabled.
    #[must_use]
    pub fn proof_enabled(&self) -> bool {
        self.proof.is_some()
    }

    /// Returns `true` when DRAT/LRAT proof logging is currently enabled
    /// (back-compat name).
    #[must_use]
    pub fn drat_proof_enabled(&self) -> bool {
        self.proof.is_some()
    }

    /// Returns `true` when LRAT (antecedent) proof logging is enabled.
    #[must_use]
    pub fn lrat_proof_enabled(&self) -> bool {
        self.lrat
    }

    // ======== proof connection helpers ========

    fn proof_ensure(&mut self) -> &mut crate::proof::Proof {
        self.proof.get_or_insert_with(crate::proof::Proof::new)
    }

    fn connect_drat(
        &mut self,
        path: impl AsRef<std::path::Path>,
        binary: bool,
    ) -> std::io::Result<()> {
        let s = path_to_str(path.as_ref())?;
        let tracer = if binary {
            crate::proof::DratTracer::open_binary(s)?
        } else {
            crate::proof::DratTracer::open(s)?
        };
        let clause_id = self.clause_id;
        let proof = self.proof_ensure();
        proof.begin_proof(clause_id);
        proof.connect(Box::new(tracer));
        Ok(())
    }

    /// Enable **binary** DRAT proof logging to `path`.
    pub fn enable_drat_proof_binary(
        &mut self,
        path: impl AsRef<std::path::Path>,
    ) -> std::io::Result<()> {
        self.connect_drat(path, true)
    }

    fn connect_lrat(
        &mut self,
        path: impl AsRef<std::path::Path>,
        binary: bool,
    ) -> std::io::Result<()> {
        let s = path_to_str(path.as_ref())?;
        let tracer = if binary {
            crate::proof::LratTracer::open_binary(s)?
        } else {
            crate::proof::LratTracer::open(s)?
        };
        // LRAT needs clause ids + RUP chains: switch on the bookkeeping.
        self.lrat = true;
        self.unit_clauses_idx.resize(2 * self.num_vars, 0);
        self.lrat_flags.resize(2 * self.num_vars, 0);
        let clause_id = self.clause_id;
        let proof = self.proof_ensure();
        proof.begin_proof(clause_id);
        proof.connect(Box::new(tracer));
        Ok(())
    }

    /// Enable **text** LRAT proof logging to `path`.
    pub fn enable_lrat_proof(&mut self, path: impl AsRef<std::path::Path>) -> std::io::Result<()> {
        self.connect_lrat(path, false)
    }

    /// Enable an in-memory text LRAT transcript and return its read handle.
    ///
    /// This is intended for an in-process certification gate.  It must be
    /// enabled before adding clauses so that the transcript contains the exact
    /// original clause prefix against which LRAT hints are numbered.
    #[must_use]
    pub fn enable_lrat_transcript(&mut self) -> crate::proof::LratTranscriptHandle {
        let (tracer, handle) = crate::proof::MemoryLratTracer::new();
        self.lrat = true;
        self.unit_clauses_idx.resize(2 * self.num_vars, 0);
        self.lrat_flags.resize(2 * self.num_vars, 0);
        let clause_id = self.clause_id;
        let proof = self.proof_ensure();
        proof.begin_proof(clause_id);
        proof.connect(Box::new(tracer));
        handle
    }

    /// Disable LRAT proof logging, dropping the proof tracer.
    pub fn disable_lrat_proof(&mut self) {
        self.proof = None;
    }

    /// Enable **binary** LRAT proof logging to `path`.
    pub fn enable_lrat_proof_binary(
        &mut self,
        path: impl AsRef<std::path::Path>,
    ) -> std::io::Result<()> {
        self.connect_lrat(path, true)
    }

    /// Flush all attached file tracers to disk.
    pub fn flush_proof(&mut self) {
        if let Some(proof) = &mut self.proof {
            proof.flush(false);
        }
    }

    // ======== clause-id bookkeeping ========

    /// Allocate the next monotonic clause id (`++clause_id`). Returns 0 when no
    /// proof is active (ids are meaningless without a tracer).
    fn proof_next_id(&mut self) -> i64 {
        if self.proof.is_some() {
            self.clause_id += 1;
            self.clause_id
        } else {
            0
        }
    }

    /// Record that stored clause `cid` carries LRAT id `id` (`c->id = id`).
    fn proof_set_clause_id(&mut self, cid: ClauseId, id: i64) {
        if !self.lrat {
            return;
        }
        let idx = cid.index();
        if idx >= self.clause_lrat_id.len() {
            self.clause_lrat_id.resize(idx + 1, 0);
        }
        self.clause_lrat_id[idx] = id;
    }

    /// Look up the LRAT id of stored clause `cid` (0 if unassigned/unknown).
    fn proof_clause_id(&self, cid: ClauseId) -> i64 {
        let idx = cid.index();
        if idx < self.clause_lrat_id.len() {
            self.clause_lrat_id[idx]
        } else {
            0
        }
    }

    /// Record the unit clause fixing `lit_dimacs` (a *true* DIMACS literal) as
    /// LRAT id `id` (`unit_clauses_idx[vlit(lit)] = id`).
    fn proof_set_unit_id(&mut self, lit_dimacs: i32, id: i64) {
        if !self.lrat {
            return;
        }
        let lit = Lit::from_dimacs(lit_dimacs);
        let li = lit.index();
        if li >= self.unit_clauses_idx.len() {
            let need = 2 * self.num_vars.max(lit.var().index() + 1);
            self.unit_clauses_idx.resize(need, 0);
        }
        self.unit_clauses_idx[li] = id;
    }

    /// Look up the LRAT id of the unit clause fixing *true* literal `lit_dimacs`
    /// (`unit_id(lit)` in upstream).
    fn proof_unit_id(&self, lit_dimacs: i32) -> i64 {
        debug_assert!(self.lrat);
        self.proof_unit_id_get_or_zero(lit_dimacs)
    }

    fn proof_unit_id_get_or_zero(&self, lit_dimacs: i32) -> i64 {
        if !self.lrat {
            return 0;
        }
        let lit = Lit::from_dimacs(lit_dimacs);
        let li = lit.index();
        if li < self.unit_clauses_idx.len() {
            self.unit_clauses_idx[li]
        } else {
            0
        }
    }

    /// Flush a level-0 propagation to an explicit derived unit (the principled
    /// fix that makes every level-0 literal a unit with an LRAT id, matching
    /// cadical's invariant). Called right after a literal is propagated at
    /// decision level 0: emits a derived unit `[lit]` whose RUP chain is the
    /// antecedent unit ids (already flushed – propagation is in trail order)
    /// followed by the propagating clause's id, and records the new unit id.
    ///
    /// This lets conflict analysis, the empty-clause walk, and minimization
    /// reference any level-0 literal by a single unit id instead of re-walking
    /// its reason sub-graph.
    pub(super) fn flush_level0_unit(&mut self, lit: Lit, cid: ClauseId) {
        if !self.lrat || self.proof.is_none() {
            return;
        }
        let lit_dimacs = lit.to_dimacs();
        if self.proof_unit_id_get_or_zero(lit_dimacs) != 0 {
            return; // already a recorded unit (original/learned unit or already flushed)
        }
        // Chain: [unit id of each antecedent's true form] ++ [propagating clause id].
        // Under ¬lit the antecedent units make the reason clause's antecedent
        // literals false, so the reason clause is fully falsified → conflict.
        let reason_lits: SmallVec<[Lit; 8]> = self
            .clauses
            .get(cid)
            .map(|c| c.lits.iter().copied().collect())
            .unwrap_or_default();
        let mut chain: SmallVec<[i64; 8]> = SmallVec::new();
        for &l in &reason_lits {
            if l.var() == lit.var() {
                continue; // the propagated literal
            }
            let v = l.var();
            let true_dimacs = if self.trail.lit_value(Lit::pos(v)).is_true() {
                Lit::pos(v).to_dimacs()
            } else {
                Lit::neg(v).to_dimacs()
            };
            chain.push(self.proof_unit_id(true_dimacs));
        }
        chain.push(self.proof_clause_id(cid));
        let id = self.proof_next_id();
        self.proof_set_unit_id(lit_dimacs, id);
        if let Some(proof) = &mut self.proof {
            proof.add_derived_unit_clause(id, lit_dimacs, &chain);
        }
    }

    // ======== higher-level proof events used by learn.rs / inprocessing ========

    /// Emit a derived clause for a *theory* lemma / explanation clause
    /// (`add_derived_clause` with an empty RUP chain). Pure-SAT runs never hit
    /// this; CDCL(T) LRAT would need the theory layer to supply a real chain.
    fn proof_theory_clause(&mut self, dimacs: &[i32]) -> i64 {
        if self.proof.is_none() {
            return 0;
        }
        let id = self.proof_next_id();
        if let Some(proof) = &mut self.proof {
            proof.add_derived_clause(id, false, dimacs, &[]);
        }
        id
    }

    /// Emit a derived *unit* theory lemma and record its unit id.
    fn proof_theory_unit(&mut self, unit_dimacs: i32) -> i64 {
        if self.proof.is_none() {
            return 0;
        }
        let id = self.proof_next_id();
        self.proof_set_unit_id(unit_dimacs, id);
        if let Some(proof) = &mut self.proof {
            proof.add_derived_unit_clause(id, unit_dimacs, &[]);
        }
        id
    }

    /// Emit a *learned* clause's derived-clause proof event: unit clauses go
    /// through the unit variant and get a unit-id table entry; multi-literal
    /// clauses go through the plain variant. The RUP chain is taken from
    /// [`Solver::lrat_chain`] (assembled by `analyze`/`minimize`). Returns the
    /// allocated id (0 if inactive) so the caller can bind it to the stored
    /// clause via [`Solver::proof_set_clause_id`].
    pub(super) fn proof_learn_clause(&mut self, lits: &[Lit]) -> i64 {
        if self.proof.is_none() {
            return 0;
        }
        let id = self.proof_next_id();
        let chain = if self.lrat {
            let c = std::mem::take(&mut self.lrat_chain);
            // A 0 hint id means a clause/unit id was never bound – the proof
            // would be un-checkable. Catch it early in debug builds.
            debug_assert!(
                !c.contains(&0),
                "zero-id hint in derived clause {} (lits={:?})",
                id,
                lits.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>()
            );
            c
        } else {
            Vec::new()
        };
        if lits.len() == 1 {
            let unit = lits[0].to_dimacs();
            self.proof_set_unit_id(unit, id);
            if let Some(proof) = &mut self.proof {
                proof.add_derived_unit_clause(id, unit, &chain);
            }
        } else {
            let dimacs: SmallVec<[i32; 16]> = lits.iter().map(|l| l.to_dimacs()).collect();
            if let Some(proof) = &mut self.proof {
                proof.add_derived_clause(id, false, &dimacs, &chain);
            }
        }
        id
    }

    /// Emit a clause *strengthen* (in-place shortening) as a proof event: add a
    /// fresh derived clause with the kept literals, then delete the old clause,
    /// finally rebind the stored clause's LRAT id to the new one
    /// (`c->id = new_id` in upstream's `strengthen_clause`). The RUP chain is
    /// empty – used by vivification, which proves the shorter clause is
    /// RUP-derivable but does not currently expose its antecedents.
    fn proof_strengthen_clause(&mut self, cid: ClauseId, kept: &[Lit]) {
        if self.proof.is_none() {
            return;
        }
        let old_id = self.proof_clause_id(cid);
        let kept_dimacs: SmallVec<[i32; 8]> = kept.iter().map(|l| l.to_dimacs()).collect();
        let old_dimacs: SmallVec<[i32; 8]> = self
            .clauses
            .get(cid)
            .map(|c| c.lits.iter().map(|l| l.to_dimacs()).collect())
            .unwrap_or_default();
        let new_id = self.proof_next_id();
        if let Some(proof) = &mut self.proof {
            proof.strengthen_clause(new_id, false, &kept_dimacs, &[]);
            proof.delete_clause(old_id, false, &old_dimacs);
        }
        self.proof_set_clause_id(cid, new_id);
    }

    /// Emit a clause deletion by stored-clause id, reading its literals before
    /// the clause is detached (no-op when proof logging is off or the clause is
    /// already gone). For LRAT the deletion is keyed by the clause's LRAT id;
    /// for DRAT it is keyed by the literal set.
    pub(super) fn drat_delete(&mut self, clause_id: ClauseId) {
        if self.proof.is_none() {
            return;
        }
        let lits: Option<SmallVec<[Lit; 8]>> = self
            .clauses
            .get(clause_id)
            .filter(|c| !c.deleted)
            .map(|c| c.lits.iter().copied().collect());
        let Some(lits) = lits else { return };
        let dimacs: SmallVec<[i32; 8]> = lits.iter().map(|l| l.to_dimacs()).collect();
        let id = self.proof_clause_id(clause_id);
        if let Some(proof) = &mut self.proof {
            proof.delete_clause(id, false, &dimacs);
        }
    }

    /// Emit a clause deletion by an explicit literal set (used when a clause is
    /// strengthened in place and its pre-strengthening form must be retired).
    pub(super) fn drat_delete_lits(&mut self, lits: &[Lit]) {
        if self.proof.is_none() {
            return;
        }
        let dimacs: SmallVec<[i32; 8]> = lits.iter().map(|l| l.to_dimacs()).collect();
        // Best-effort id: a unit's id is recoverable from the unit table.
        let id = if lits.len() == 1 {
            self.proof_unit_id_get_or_zero(lits[0].to_dimacs())
        } else {
            0
        };
        if let Some(proof) = &mut self.proof {
            proof.delete_clause(id, false, &dimacs);
        }
    }

    /// Emit the empty clause (unconditional UNSAT). For LRAT this first builds
    /// the empty clause's RUP chain from the current conflict.
    pub(super) fn drat_emit_empty(&mut self, conflict: Option<ClauseId>) {
        if self.proof.is_none() || self.lrat_finalized {
            return;
        }
        if self.lrat {
            self.build_chain_for_empty(conflict);
        }
        self.finalize_empty_clause();
    }

    /// Emit the empty clause whose derivation is seeded by an explicit,
    /// already-fully-falsified clause given as literals + its LRAT `final_id`.
    ///
    /// This is the `add_clause`-level counterpart of [`Self::drat_emit_empty`]:
    /// the contradiction is detected *before* the offending clause is attached
    /// to the clause database (so no `ClauseId` exists yet for
    /// [`Self::build_chain_for_empty`] to read), but the clause is fully
    /// falsified at decision level 0 – every literal's negation is a level-0
    /// unit with a known LRAT id – so the RUP chain is simply
    /// `[unit id of each literal's negation] ++ [final_id]`, which is exactly
    /// what `build_chain_for_empty(Some(cid))` computes for a stored clause.
    /// Faithful port of v0.3.2's `lrat_emit_empty_from(seed_lits, final_id)`;
    /// v0.3.2's general `lrat_build_hint_chain` reduces to this same chain for
    /// a level-0-falsified clause (no deeper antecedents to recurse into).
    pub(super) fn drat_emit_empty_from_seed(&mut self, seed_lits: &[Lit], final_id: i64) {
        if self.proof.is_none() || self.lrat_finalized {
            return;
        }
        if self.lrat {
            // Same per-literal walk as `build_chain_for_empty`, but driven by
            // the explicit seed literals + id rather than a stored ClauseId.
            debug_assert!(
                self.lrat_chain.is_empty(),
                "lrat_chain must be clean before seeding the empty-clause chain"
            );
            for lit in seed_lits {
                // `lit` is falsified; its negation is the level-0 unit fixing it.
                self.lrat_chain
                    .push(self.proof_unit_id(lit.negate().to_dimacs()));
            }
            self.lrat_chain.push(final_id);
        }
        self.finalize_empty_clause();
    }

    /// Shared tail of the two empty-clause emitters above: allocate the id,
    /// drain `lrat_chain` as the RUP hints (empty for DRAT-only), append the
    /// derived empty clause, and mark the proof finalized so every subsequent
    /// proof hook is a no-op.
    fn finalize_empty_clause(&mut self) {
        let id = self.proof_next_id();
        let chain = if self.lrat {
            std::mem::take(&mut self.lrat_chain)
        } else {
            Vec::new()
        };
        if let Some(proof) = &mut self.proof {
            proof.add_derived_empty_clause(id, &chain);
        }
        self.lrat_chain.clear();
        // The empty clause finalizes the proof: no further additions can
        // affect verification (a checker stops reading at the empty clause),
        // and a caller reusing the solver must not keep appending to a
        // concluded proof. Mirrors v0.3.2's finalization. Flush immediately
        // so a caller that reads the proof file before dropping the solver
        // (and so before BufWriter's drop-flush) sees the concluded proof –
        // matches v0.3.2's `writer.flush()` in `lrat_emit_empty_from`.
        self.flush_proof();
        self.lrat = false;
        self.lrat_finalized = true;
    }

    /// Purge every binary-implication-graph edge belonging to `clause_id`.
    ///
    /// The binary graph is a direct-index fast path over binary clauses; unlike
    /// the watch lists (which lazily skip deleted clauses) it is consulted
    /// without a liveness check at its call sites' hot loop, so a retracted
    /// binary clause must have its edges physically removed. Reads the clause's
    /// literals, so it must run *before* the clause is removed from the database.
    pub(super) fn purge_binary_edges(&mut self, clause_id: ClauseId) {
        let binary_lits = self.clauses.get(clause_id).and_then(|c| {
            if c.lits.len() == 2 && !c.deleted {
                Some((c.lits[0], c.lits[1]))
            } else {
                None
            }
        });
        if let Some((a, b)) = binary_lits {
            self.binary_graph.remove_clause_edges(a.negate(), clause_id);
            self.binary_graph.remove_clause_edges(b.negate(), clause_id);
        }
    }

    /// Attach a cooperative interrupt flag.
    ///
    /// While solving, the CDCL loop periodically checks this flag; if another
    /// thread sets it to `true`, the current `solve*` call abandons the search
    /// and returns [`SolverResult::Unknown`]. Combined with
    /// [`Solver::set_max_conflicts`], this lets callers bound solving by both
    /// wall-clock time (via an external timer that sets the flag) and work.
    pub fn set_interrupt(&mut self, flag: Arc<AtomicBool>) {
        self.interrupt = Some(flag);
    }

    /// Set the conflict budget (`None` clears it). When set, the CDCL search
    /// loop returns [`SolverResult::Unknown`] once the budget is reached.
    pub fn set_max_conflicts(&mut self, max_conflicts: Option<u64>) {
        self.max_conflicts = max_conflicts;
    }

    /// The current conflict budget ([`Self::set_max_conflicts`]); `None`
    /// means unlimited.  Portfolio drivers use it to compose per-arm caps
    /// with a caller-supplied global budget.
    #[must_use]
    pub fn max_conflicts(&self) -> Option<u64> {
        self.max_conflicts
    }

    /// Update the search-schedule fields on a **live** solver (the portfolio
    /// driver's diversity levers).
    ///
    /// `restart_strategy`, `enable_inprocessing` and `inprocessing_interval`
    /// are read live by the restart and inprocessing schedules
    /// (`Solver::restart`, `Solver::handle_clause_deletion_and_restart`) –
    /// not baked at construction – so re-setting them between solves changes
    /// the next solve's search behaviour. This closes the gap where a caller
    /// replacing a configuration through a higher layer (SMT
    /// `set_solver_config`, portfolio strategies) got these fields stored
    /// but never consumed, because this engine had already been built.
    ///
    /// Construction-time state is deliberately untouched: chronological-
    /// backtracking thresholds, the initial stabilization schedule and the
    /// eliminator's limits are seeded into helper structures by
    /// [`Solver::with_config`], and re-setting those mid-flight would desync
    /// their bookkeeping.
    pub fn update_search_config(
        &mut self,
        restart_strategy: RestartStrategy,
        enable_inprocessing: bool,
        inprocessing_interval: u64,
    ) {
        self.config.restart_strategy = restart_strategy;
        self.config.enable_inprocessing = enable_inprocessing;
        self.config.inprocessing_interval = inprocessing_interval;
    }

    /// Read-only view of the live solver configuration.
    #[must_use]
    pub fn config(&self) -> &SolverConfig {
        &self.config
    }

    /// Set the preferred (default) decision phase for a variable.
    ///
    /// Used by theory-combination axiomatization (the z3-style "triangle"
    /// axioms `(t1=t2) ⟺ (t1≤t2 ∧ t1≥t2)`): biasing the equality atom toward
    /// `true` (`try_true_first`) makes CDCL prefer merging shared terms, so the
    /// arithmetic solver's consistency check (`check`) – not fragile reason
    /// extraction – drives theory combination.
    pub fn set_preferred_phase(&mut self, var: Var, phase: bool) {
        let idx = var.index();
        if idx < self.phase.len() {
            self.phase[idx] = phase;
        }
        if idx < self.best_phase.len() {
            self.best_phase[idx] = phase;
        }
        if idx < self.target_phase.len() {
            self.target_phase[idx] = phase;
        }
    }

    /// Theory-aware decision hint: bump the activity of these variables so
    /// the branching heuristic prefers deciding them early.  Mirrors the
    /// per-conflict bump in conflict.rs so it works under every strategy.
    pub fn bump_decision_hint(&mut self, vars: &[Var]) {
        if vars.is_empty() {
            return;
        }
        self.vsids.bump_batch(vars);
        if self.config.use_chb_branching {
            self.chb.bump_batch(vars);
        }
        if self.config.use_vmtf {
            for &v in vars {
                self.vmtf.bump(v, |v| self.trail.is_assigned(v));
            }
        }
    }

    /// Set a theory-derived deterministic decision phase for `var`.
    ///
    /// This is stronger than [`Self::set_preferred_phase`] only as a search
    /// heuristic: random polarity and global rephasing do not replace it.
    /// It does not assign the variable or constrain the Boolean problem.
    pub fn set_deterministic_phase(&mut self, var: Var, phase: bool) {
        if let Some(slot) = self.deterministic_phase.get_mut(var.index()) {
            *slot = Some(phase);
        }
        self.set_preferred_phase(var, phase);
    }

    /// Choose a decision polarity, honoring a coherent theory posture before
    /// the generic randomized phase-saving heuristic.
    /// cadical `decide_phase (idx, target)`: forced (theory-deterministic)
    /// phase first, then the target phase while it is active (stable mode
    /// under the default `target = 1`, always under `target = 2`), then the
    /// saved phase.  The random-polarity perturbation is an OxiZ extension
    /// applied on top of the cadical source polarity, exactly where it used
    /// to apply to the saved phase alone.
    fn decision_polarity(&mut self, var: Var) -> bool {
        if let Some(phase) = self.deterministic_phase.get(var.index()).copied().flatten() {
            return phase;
        }
        let source = if self.target_phase_active() {
            self.target_phase.get(var.index()).copied()
        } else {
            None
        };
        let rand_p = if self.stable {
            self.config
                .random_polarity_prob_stable
                .unwrap_or(self.config.random_polarity_prob)
        } else {
            self.config.random_polarity_prob
        };
        if self.rand_bool(rand_p) {
            self.rand_bool(0.5)
        } else {
            source
                .or_else(|| self.phase.get(var.index()).copied())
                .unwrap_or(false)
        }
    }

    /// cadical `const bool target = (opts.target > 1 || (stable && opts.target))`.
    fn target_phase_active(&self) -> bool {
        self.config.target > 1 || (self.stable && self.config.target == 1)
    }

    /// Raise VSIDS activity so `var` is decided early.
    ///
    /// Used after finite-domain case-splits on table indices: once those
    /// equalities are fixed, lookup tables unit-propagate and the remaining
    /// arithmetic is nearly determined.
    pub fn bump_var_activity(&mut self, var: Var, times: u32) {
        if !self.vsids.contains(var) {
            self.vsids.insert(var);
        }
        for _ in 0..times {
            self.vsids.bump(var);
        }
    }

    /// Install (or replace) an external branching heuristic.
    pub fn set_external_branching(&mut self, h: crate::solver::BoxedBranchingHeuristic) {
        self.config.external_branching = Some(h);
    }

    /// Variables to decide before VSIDS (highest priority first).
    ///
    /// Finite-domain table-index equalities: O(|priority|) per decision instead
    /// of scanning all unassigned vars via external branching.
    pub fn set_domain_priority(&mut self, vars: Vec<Var>) {
        self.domain_priority = vars;
    }

    /// Returns `true` when the search must stop early: the conflict budget has
    /// been reached or an external interrupt flag has been raised.
    #[inline]
    pub(super) fn should_stop_search(&self) -> bool {
        if let Some(max) = self.max_conflicts
            && self.stats.conflicts >= max
        {
            return true;
        }
        if let Some(flag) = &self.interrupt
            && flag.load(Ordering::Relaxed)
        {
            return true;
        }
        false
    }

    /// Create a new variable
    pub fn new_var(&mut self) -> Var {
        let var = Var::new(self.num_vars as u32);
        self.num_vars += 1;
        self.trail.resize(self.num_vars);
        self.watches.resize(self.num_vars);
        self.binary_graph.resize(self.num_vars);
        self.vsids.insert(var);
        self.chb.insert(var);
        self.vmtf.resize(self.num_vars);
        self.lrb.resize(self.num_vars);
        self.seen.resize(self.num_vars, false);
        self.model.resize(self.num_vars, LBool::Undef);
        self.phase.resize(self.num_vars, false); // Default phase: negative
        self.deterministic_phase.resize(self.num_vars, None);
        self.best_phase.resize(self.num_vars, false);
        self.target_phase.resize(self.num_vars, false);
        // Resize level_marks to at least num_vars (enough for decision levels)
        if self.level_marks.len() < self.num_vars {
            self.level_marks.resize(self.num_vars, 0);
        }
        // Per-decision-level `seen` statistics for clause minimization
        // (cadical `Level::seen`): decision levels are bounded by num_vars.
        if self.seen_level_count.len() < self.num_vars {
            self.seen_level_count.resize(self.num_vars, 0);
            self.seen_level_trail.resize(self.num_vars, u32::MAX);
        }
        // Grow the per-literal tables.  `lrat_flags` holds the
        // KEEP/POISON/REMOVABLE minimization flags (see `conflict.rs`) and is
        // used by BOTH the plain and the LRAT minimizers – with the table
        // empty the plain minimizer degenerates to keeping every literal,
        // since the flags can never persist between candidates.
        // `unit_clauses_idx` is only needed while an LRAT tracer is connected.
        if self.lrat {
            self.unit_clauses_idx.resize(2 * self.num_vars, 0);
        }
        self.lrat_flags.resize(2 * self.num_vars, 0);
        // Elimination state tables (candidates are marked lazily when one of
        // their clauses is touched; the pre-search phase marks everything).
        self.elim_mark.resize(self.num_vars, false);
        self.elim_var_flag.resize(self.num_vars, false);
        self.probe_propfixed.resize(2 * self.num_vars, -1);
        var
    }

    /// Export the current SAT problem (every live clause plus every level-0
    /// trail literal as a unit clause) in DIMACS int-literal encoding
    /// (1-based, sign = polarity), together with the variable count. Used to
    /// hand the problem to an external SAT backend.
    pub fn export_problem_dimacs(&self) -> (usize, Vec<Vec<i32>>) {
        let mut clauses: Vec<Vec<i32>> = Vec::new();
        // Level-0 trail literals are the unconditional assertions; an external
        // solver needs them as unit clauses.
        for lit in self.trail.assignments() {
            if self.trail.level(lit.var()) == 0 {
                clauses.push(vec![lit.to_dimacs()]);
            }
        }
        for id in self.clauses.iter_ids() {
            let Some(c) = self.clauses.get(id) else {
                continue;
            };
            if c.deleted {
                continue;
            }
            clauses.push(c.lits.iter().map(|l| l.to_dimacs()).collect());
        }
        (self.num_vars, clauses)
    }

    /// Ensure we have at least n variables
    pub fn ensure_vars(&mut self, n: usize) {
        while self.num_vars < n {
            self.new_var();
        }
    }

    /// Scan `clause_lits` against the *current* trail: is any literal true,
    /// what is the highest level among the false literals (0 if there are
    /// none), and which literals are still undefined.
    ///
    /// Read-only. Used by [`Solver::pre_check_effective_unit`] both before
    /// and (when it backtracks) after a `backtrack_to_root()` call, so it
    /// must not itself assume anything about levels.
    fn scan_clause_for_attach(&self, clause_lits: &[Lit]) -> (bool, u32, SmallVec<[Lit; 4]>) {
        // A literal assigned at decision level >= 1 is *non-permanent*: the
        // search can backtrack past it, turning a `true` into `undef` (or a
        // `false` into `undef`).  For deciding whether a clause being attached
        // is *permanently* satisfied / unit / conflicting – the question
        // [`pre_check_effective_unit`] answers – only level-0 facts count.
        // A clause "satisfied" solely by a level->=1 literal is not really
        // satisfied: once that literal is backtracked the clause may become a
        // unit or conflict, and the watch / binary-implication machinery
        // cannot re-discover it, because a level-0 *false* sibling's
        // negation was already dequeued when it was assigned and is never
        // re-fired.  Treating a level->=1 `true` literal as undefined here
        // makes the effective-unit analysis see that latent unit and force it
        // at level 0 now, instead of leaving a hanging unit for the search
        // to trip over after a backtrack.  (Level->=1 *false* literals keep
        // their level: `pre_check_effective_unit` backtracks to root and
        // re-scans when it sees `max_false_level > 0`, which turns them into
        // undefined too.)
        let mut has_true = false;
        let mut max_false_level = 0u32;
        let mut undefined: SmallVec<[Lit; 4]> = SmallVec::new();
        for &lit in clause_lits {
            let value = self.trail.lit_value(lit);
            if value.is_true() {
                if self.trail.level(lit.var()) == 0 {
                    has_true = true;
                    break;
                } else {
                    // Non-permanent satisfaction: backtrackable, so it does
                    // not make the clause permanently satisfied.
                    undefined.push(lit);
                }
            } else if value.is_false() {
                max_false_level = max_false_level.max(self.trail.level(lit.var()));
            } else {
                undefined.push(lit);
            }
        }
        (has_true, max_false_level, undefined)
    }

    /// Resolve `clause_lits`'s conflict / effective-unit status against the
    /// current trail, performing any necessary backtrack, *before* the
    /// caller chooses which literals to watch.
    ///
    /// # Why this must run before watch selection
    ///
    /// The two-watched-literal ranking (`watch_rank` and its call sites in
    /// `add_clause`) is computed against whatever the trail looks like when
    /// it runs. A `backtrack_to_root()` performed *after* that ranking would
    /// silently invalidate it: literals the ranking saw as false may now be
    /// undefined, so the "watch the two latest-falsified literals" choice it
    /// made is no longer meaningful. Running this check first, and letting
    /// its backtrack (if any) land before ranking ever executes, keeps the
    /// two steps consistent with each other.
    ///
    /// # Why "effectively unit" needs the same treatment as "all false"
    ///
    /// A clause is only safe to attach as-is when every literal that is
    /// currently false is false *permanently* (at level 0). A literal false
    /// above level 0 can be unassigned by a future backtrack while some
    /// *other* disjunct of the clause survives (in particular, an implied
    /// literal this same function forces at the wrong level would -- see the
    /// history of this function for the bug that motivated this rewrite):
    /// the clause is then silently reopened, with no live watcher able to
    /// notice, because watch/graph registration only fires on a literal's
    /// *next* transition, not because of anything a backtrack does. This is
    /// true whether the clause is fully false (a conflict) or has exactly
    /// one literal left undefined (an effective unit) -- both are handled by
    /// the same rule here.
    ///
    /// `backtrack_to_root()` resolves the ambiguity outright: every literal
    /// false above level 0 becomes undefined, so a mandatory re-scan
    /// afterward finds either 2+ undefined literals (ordinary watching is
    /// then correct and sufficient -- the clause is genuinely open again) or
    /// still at most one undefined literal, with every remaining false
    /// literal now unconditionally at level 0 (forced at level 0, which
    /// survives every future backtrack by construction).
    fn pre_check_effective_unit(&mut self, clause_lits: &[Lit]) -> PreAttachOutcome {
        let (has_true, max_false_level, undefined) = self.scan_clause_for_attach(clause_lits);
        if has_true || undefined.len() >= 2 {
            return PreAttachOutcome::Ordinary;
        }

        if max_false_level > 0 {
            self.backtrack_to_root();
            // Mandatory re-scan: the sets computed above are now stale.
            let (has_true, _post_backtrack_max_level, undefined) =
                self.scan_clause_for_attach(clause_lits);
            debug_assert!(
                !has_true,
                "backtrack_to_root() cannot turn a false/undefined literal true"
            );
            return if undefined.is_empty() {
                PreAttachOutcome::UnconditionalConflict
            } else if undefined.len() == 1 {
                PreAttachOutcome::ForceUnitAtLevelZero(undefined[0])
            } else {
                PreAttachOutcome::Ordinary
            };
        }

        if undefined.is_empty() {
            PreAttachOutcome::UnconditionalConflict
        } else {
            // Force the unit *physically* at level 0: main's simple-pop trail
            // removes by position, so appending this permanent fact at a higher
            // level would let the next backtrack pop it. max_false_level == 0
            // here, so no clause literal sits above level 0 and `undefined` is
            // unchanged by the backtrack.
            if self.trail.decision_level() > 0 {
                self.backtrack_to_root();
            }
            PreAttachOutcome::ForceUnitAtLevelZero(undefined[0])
        }
    }

    /// Add a clause
    pub fn add_clause(&mut self, lits: impl IntoIterator<Item = Lit>) -> bool {
        let mut clause_lits: SmallVec<[Lit; 8]> = lits.into_iter().collect();

        // Gatekeeper (SK-1): if equivalent-literal substitution folded a
        // variable away, rewrite any reintroduced mention of it through the
        // substitution map to its class representative. Without this a later
        // clause naming an ELS-eliminated variable would branch on it as a
        // free variable (the equivalence is no longer in the live clause set),
        // yielding a false `Sat`. No-op when ELS has not run (empty map).
        for lit in clause_lits.iter_mut() {
            *lit = self.resolve_reintroduced_literal(*lit);
        }

        // Ensure we have all variables
        for lit in &clause_lits {
            let var_idx = lit.var().index();
            if var_idx >= self.num_vars {
                self.ensure_vars(var_idx + 1);
            }
        }

        // Assign this original clause a monotonic LRAT id *before* any
        // early-return (tautology / unit / empty), so every input clause draws
        // exactly one id in file order – matching `lrat-check`'s CNF numbering
        // (`1..K`). `0` when no proof is active. The id is bound to a stored
        // clause / unit entry below; tautologies consume it but bind nothing.
        let proof_oid = if self.proof.is_some() {
            let id = self.proof_next_id();
            let dimacs: SmallVec<[i32; 8]> = clause_lits.iter().map(|l| l.to_dimacs()).collect();
            if let Some(proof) = &mut self.proof {
                proof.add_original_clause(id, false, &dimacs);
            }
            id
        } else {
            0
        };

        // Remove duplicates and check for tautology
        clause_lits.sort_by_key(|l| l.code());
        clause_lits.dedup();

        // Check for tautology (x and ~x in same clause).  Complementary
        // literals have adjacent codes (`2*var` / `2*var + 1`), so after the
        // sort a tautological pair is always adjacent: one linear pass.  The
        // previous all-pairs scan was quadratic in the clause length and
        // dominated `add_clause` on bit-blasted CNFs with long clauses.
        for w in clause_lits.windows(2) {
            if w[0] == w[1].negate() {
                return true; // Tautology - always satisfied
            }
        }

        // Handle special cases
        match clause_lits.len() {
            0 => {
                self.trivially_unsat = true;
                return false; // Empty clause - unsat
            }
            1 => {
                // Unit clause - enqueue at decision level 0
                // Unit clauses must be assigned at level 0 to survive backtracking.
                // After solve(), current_level may be > 0, so we must backtrack first.
                let lit = clause_lits[0];

                // Record the unit clause's LRAT id against its true literal so it
                // can be referenced as an antecedent in RUP chains (`assign_original_unit`).
                self.proof_set_unit_id(lit.to_dimacs(), proof_oid);

                if self.trail.lit_value(lit).is_false() {
                    // The literal conflicts with the current trail.
                    // Check if the conflict is at decision level 0 (permanent constraint)
                    // or from a previous solve (can be retried after backtrack).
                    let var = lit.var();
                    let level = self.trail.level(var);
                    if level == 0 {
                        // Conflict with a level-0 assignment - truly UNSAT.
                        // The new unit clause and the existing level-0 fact it
                        // contradicts together already contain the empty
                        // clause: emit it now, seeded by this clause's own
                        // literal (fully falsified) and id, rather than
                        // deferring to `solve()`'s `drat_emit_empty(None)`
                        // (which would emit an empty, unverifiable chain).
                        // Faithful port of v0.3.2's `add_clause` unit-conflict
                        // branch.
                        self.trivially_unsat = true;
                        self.drat_emit_empty_from_seed(&[lit], proof_oid);
                        return false;
                    } else {
                        // Conflict with higher-level assignment from previous solve.
                        // Backtrack to root and assign the new unit literal at level 0.
                        self.backtrack_to_root();
                        self.trail.assign_decision(lit);
                        return true;
                    }
                }

                if self.trail.lit_value(lit).is_true() {
                    // Already satisfied - check if at level 0
                    let var = lit.var();
                    let level = self.trail.level(var);
                    if level == 0 {
                        // Already assigned at level 0, nothing to do
                        return true;
                    }
                    // Assigned at higher level - backtrack and reassign at level 0
                    self.backtrack_to_root();
                    self.trail.assign_decision(lit);
                    return true;
                }

                // Variable is unassigned - backtrack to level 0 first to ensure
                // the assignment is at level 0 (survives future backtracks)
                if self.trail.decision_level() > 0 {
                    self.backtrack_to_root();
                }
                self.trail.assign_decision(lit);
                return true;
            }
            2 => {
                // Binary clause - check if it conflicts with current assignment
                let lit0 = clause_lits[0];
                let lit1 = clause_lits[1];
                let val0 = self.trail.lit_value(lit0);
                let val1 = self.trail.lit_value(lit1);

                // If the clause is *permanently* satisfied (by a level-0
                // literal), just add it.  Satisfaction by a level->=1 literal
                // is NOT permanent: that literal can be backtracked, and a
                // level-0 *false* sibling would then make this clause a unit
                // whose binary-implication edge (`!false_lit -> other`) never
                // re-fires (the false literal's negation was already dequeued
                // when it was assigned at level 0).  Fall through to
                // `pre_check_effective_unit`, whose level-aware scan treats
                // level->=1 satisfaction as undefined and forces such a latent
                // unit at level 0.
                let perm_satisfied = (val0.is_true() && self.trail.level(lit0.var()) == 0)
                    || (val1.is_true() && self.trail.level(lit1.var()) == 0);
                if perm_satisfied {
                    // Clause already satisfied by a permanent assignment
                    let clause_id = self.clauses.add_original(clause_lits.iter().copied());
                    self.proof_set_clause_id(clause_id, proof_oid);
                    if let Some(current_level_clauses) = self.assertion_clause_ids.last_mut() {
                        current_level_clauses.push(clause_id);
                    }
                    // BIG registration (and the phantom tick count) happens
                    // inside `attach_watchers` for binaries – BIG-authoritative
                    // BCP, 2026-09.
                    self.attach_watchers(clause_id, lit0, lit1);
                    return true;
                }

                // Resolve conflict / effective-unit status *before*
                // attaching the clause -- see `pre_check_effective_unit`'s
                // doc comment for the full reasoning (in particular why an
                // "effectively unit" binary clause, not just an "all false"
                // one, needs its level bookkeeping resolved this way: the
                // watches registered below cannot be trusted to discover it
                // on their own, since they only fire on a literal's *next*
                // transition -- a level-0 fact from earlier in this
                // incremental session was already dequeued long ago and will
                // never be dequeued again).
                let outcome = self.pre_check_effective_unit(&clause_lits);
                if matches!(outcome, PreAttachOutcome::UnconditionalConflict) {
                    // This just-registered binary clause is itself fully
                    // falsified at level 0 – seed the empty-clause derivation
                    // from its own literals + id (faithful port of v0.3.2's
                    // binary branch).
                    self.trivially_unsat = true;
                    self.drat_emit_empty_from_seed(&clause_lits, proof_oid);
                    return false;
                }

                let clause_id = self.clauses.add_original(clause_lits.iter().copied());
                self.proof_set_clause_id(clause_id, proof_oid);
                if let Some(current_level_clauses) = self.assertion_clause_ids.last_mut() {
                    current_level_clauses.push(clause_id);
                }
                // BIG registration (and the phantom tick count) happens
                // inside `attach_watchers` for binaries.
                self.attach_watchers(clause_id, lit0, lit1);

                if let PreAttachOutcome::ForceUnitAtLevelZero(forced) = outcome {
                    self.trail.assign_propagation_at(forced, clause_id, 0);
                    // LRAT: defer the unit flush to solve entry — emitting a
                    // derived unit here would allocate a *derived* id inside
                    // the original-clause prefix (which must stay contiguous
                    // 1..K in file order for the checker's CNF numbering);
                    // the collision shifted every later original's id and
                    // broke every chain referencing them (6s167, 2026-09-02).
                    self.pending_parse_unit_flushes.push((forced, clause_id));
                }
                return true;
            }
            _ => {}
        }

        // Add clause (3+ literals)
        // Resolve conflict / effective-unit status *before* choosing watches
        // -- see `pre_check_effective_unit`'s doc comment. Must run before
        // the `watch_rank` selection below: a `backtrack_to_root()` decided
        // on afterward would silently invalidate whatever ranking that
        // selection just computed.
        let outcome = self.pre_check_effective_unit(&clause_lits);
        if matches!(outcome, PreAttachOutcome::UnconditionalConflict) {
            // This just-registered 3+-literal clause is itself fully
            // falsified at level 0 – seed the empty-clause derivation from
            // its own literals + id (faithful port of v0.3.2's 3+ branch).
            self.trivially_unsat = true;
            self.drat_emit_empty_from_seed(&clause_lits, proof_oid);
            return false;
        }

        // Choose the two watch literals *before* storing the clause, following
        // MiniSat's attachClause invariant: watch the two literals that are the
        // last to become false under the current assignment. Ranking prefers a
        // true literal, then an unassigned one, and only then a false literal at
        // the highest decision level (see `watch_rank`).
        //
        // The previous code unconditionally watched `clause_lits[0..2]`. After a
        // prior `solve()` left a full trail (with `prop_head == len`), a clause
        // whose two lowest-code literals are false-but-already-propagated would
        // have both watches on false literals; those watch events never fire
        // again, so the clause could be silently falsified. A later `solve()`
        // could then return Sat on a model violating the clause, or miss a
        // conflict on an actually-UNSAT formula. Watching the two
        // latest-falsified literals restores the invariant that a watched
        // literal becoming false always re-examines the clause.
        //
        // Safe to run *after* `pre_check_effective_unit` above: any
        // `backtrack_to_root()` it performed has already happened, so this
        // ranking sees the final, post-backtrack trail state rather than one
        // that gets invalidated out from under it.
        let n = clause_lits.len();
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

        let clause_id = self.clauses.add_original(clause_lits.iter().copied());
        self.proof_set_clause_id(clause_id, proof_oid);

        // Track clause for incremental solving
        if let Some(current_level_clauses) = self.assertion_clause_ids.last_mut() {
            current_level_clauses.push(clause_id);
        }

        let lit0 = clause_lits[0];
        let lit1 = clause_lits[1];

        self.attach_watchers(clause_id, lit0, lit1);

        // `pre_check_effective_unit` already determined -- against the exact
        // pre-watch-selection trail state, before anything here could shift
        // it -- whether this clause needs its sole undefined literal forced,
        // and confirmed every false literal is a permanent level-0 fact when
        // it did. Apply that decision now that `clause_id` exists.
        if let PreAttachOutcome::ForceUnitAtLevelZero(forced) = outcome {
            self.trail.assign_propagation_at(forced, clause_id, 0);
            // LRAT: deferred like the binary branch above — see the comment
            // there for the original-prefix id-contiguity argument.
            self.pending_parse_unit_flushes.push((forced, clause_id));
        }

        true
    }

    /// Rank a literal for two-watched-literal selection; a higher rank is a
    /// better watch. A true literal is best (the clause is satisfied through it),
    /// then an unassigned literal, and finally a false literal – and among false
    /// literals the one assigned at the highest decision level (falsified latest)
    /// is preferred. Watching the two highest-ranked literals mirrors MiniSat's
    /// attachClause invariant so a watch always fires when a watched literal is
    /// (re)falsified.
    pub(super) fn watch_rank(&self, l: Lit) -> (u8, u32) {
        let v = self.trail.lit_value(l);
        if v.is_true() {
            (2, u32::MAX)
        } else if v.is_false() {
            (0, self.trail.level(l.var()))
        } else {
            (1, u32::MAX)
        }
    }

    /// Add a clause from DIMACS literals
    pub fn add_clause_dimacs(&mut self, lits: &[i32]) -> bool {
        self.add_clause(lits.iter().map(|&l| Lit::from_dimacs(l)))
    }

    /// Decay clause activity the MiniSat way: grow the per-conflict bump
    /// increment (so recently-useful clauses dominate) instead of multiplying
    /// every clause's activity on every conflict. Rescale only when the
    /// increment approaches the f64 range limit – a rare O(n) pass that
    /// replaces what was an O(n) pass *every* conflict (a top flamegraph
    /// hotspot). The only active consumer of clause activity is
    /// `reduce_clause_database`, which ranks clauses relatively, so the
    /// implicit decay preserves correctness.
    pub(super) fn decay_clause_activity(&mut self) {
        self.clause_bump_increment /= self.config.clause_decay;
        if self.clause_bump_increment > 1e20 {
            const FACTOR: f64 = 1e-20;
            self.clauses.rescale_activity(FACTOR as f32);
            self.clause_bump_increment *= FACTOR;
        }
    }

    /// Decay the VSIDS score increment, honoring the mode-gating study
    /// switches (`bump_mode_gate_enabled` / `..._null_enabled`): cadical
    /// grows `score_inc` only while scores are the active heuristic
    /// (`analyze.cpp::bump_variable_score_inc` under `use_scores ()`), so
    /// under the gate the increment stays flat through focused phases and
    /// stable-mode EVSIDS ordering is not seeded by focused-phase pollution.
    /// Default (gates unset): unconditional, historical behavior.
    pub(super) fn decay_vsids(&mut self) {
        let scores_active = !self.config.use_vmtf || !self.config.focused_vmtf || self.stable;
        let gated = crate::bump_mode_gate_enabled() || crate::bump_mode_gate_null_enabled();
        if scores_active || !gated {
            self.vsids.decay();
        }
    }

    /// The fatal soundness error set by a prior `add_clause`/assumption that
    /// reintroduced a BVE-eliminated variable (`None` when none has). When
    /// `Some`, `solve*` returns `Unknown` rather than guess.
    #[must_use]
    pub fn error(&self) -> Option<&SolverError> {
        self.fatal_error.as_ref()
    }

    /// Solve the currently registered clause set without assumptions.
    pub fn solve(&mut self) -> SolverResult {
        // A prior `add_clause` reintroduced a BVE-eliminated variable with no
        // sound way to honor it: refuse rather than risk a wrong verdict.
        if self.fatal_error.is_some() {
            return SolverResult::Unknown;
        }
        // LRAT: emit the derived units that `add_clause`'s effective-unit
        // path deferred during parsing. Safe here — the original-clause
        // prefix is complete, so these derived ids start past it. Must run
        // before the initial propagation below: that propagate's own unit
        // flushes reference these literals as antecedents, and the search's
        // first RUP chains reference their unit ids.
        if !self.pending_parse_unit_flushes.is_empty() {
            let pending = core::mem::take(&mut self.pending_parse_unit_flushes);
            for (lit, cid) in pending {
                self.flush_level0_unit(lit, cid);
            }
        }
        // Check if trivially unsatisfiable
        if self.trivially_unsat {
            self.drat_emit_empty(None);
            return SolverResult::Unsat;
        }

        // Initial propagation
        if let Some(conflict) = self.propagate() {
            // The conflict clause is required to seed the LRAT hint chain for
            // the final empty clause. Dropping it emitted `0 0` after initial
            // propagation, which is not a proof even though the verdict is
            // genuinely UNSAT.
            self.drat_emit_empty(Some(conflict));
            return SolverResult::Unsat;
        }

        // Cancellation entry gate (cadical `terminated_asynchronously` at
        // loop top, hoisted to the pre-search phase): a flag already raised
        // before `solve()` must abandon *before* the preprocessing passes,
        // not after burning through their budgets. The search loop re-checks
        // every iteration; the passes themselves are budgeted, so a flag
        // raised mid-preprocessing is honored at the latest when the loop is
        // entered.
        if self.should_stop_search() {
            return SolverResult::Unknown;
        }

        // Lucky pre-solving (CaDiCaL `lucky_phases`): try to satisfy the
        // formula without search via a small set of structured phase guesses
        // (uniform / Horn / ordered-with-flip). On by default, matching
        // CaDiCaL – each strategy is soundness-preserving (a pure scan or a
        // single-literal-at-a-time probe that bails to the root on failure, so
        // a doomed guess never perturbs the watched-literal state).
        if self.config.enable_lucky {
            match self.lucky_phases() {
                Some(SolverResult::Sat) => {
                    self.save_model();
                    return SolverResult::Sat;
                }
                Some(SolverResult::Unsat) => return SolverResult::Unsat,
                _ => {}
            }
        }

        // Bounded variable elimination (cadical `elim.cpp` port,
        // `solver/eliminate.rs`): collapses the original clause set via
        // resolution + interleaved subsumption rounds before search, with a
        // growing elimination bound. Re-armed mid-search from the conflict
        // handler whenever new units or removed/shrunken original clauses
        // appear. Runs at level 0 / base scope only. Scheduled *after* lucky
        // pre-solving: a lucky guess is a pure scan that answers some
        // structured families (Simon) in microseconds, which the elimination
        // phase would otherwise bury under seconds of occurrence-list work
        // before the guess ever runs.
        // Conflict scheduling (cadical parity, see
        // `SolverConfig::presearch_collapse`): with the default `false`, the
        // pre-search fixpoint, the ELS one-shot and the inprocess/vivify
        // pre-passes are all skipped; the conflict handlers schedule them
        // instead (`eliminating()`'s first-phase arm fires once `lim_elim`
        // is crossed, and `try_scheduled_elimination` runs the one-shot ELS
        // alongside the first phase).
        let sched_parity = !self.config.presearch_collapse;

        if self.config.enable_bve && !sched_parity {
            // Iterate elimination phases to a fixpoint before search
            // (cadical's preprocessing interleaves elim/subsume rounds
            // back-to-back; a single bound-0 phase leaves most of the
            // collapse on the table and the mid-search schedule then waits
            // `elim_interval * (phases + 1)` conflicts for the next one).
            // Each completed phase grows the elimination bound and re-marks
            // every variable, so `eliminate_phase` itself reports when
            // another phase is worth running via `eliminating()`.
            while self.eliminating_presearch() {
                if self.eliminate_phase() == equiv::SubstOutcome::Unsat {
                    self.drat_emit_empty(None);
                    return SolverResult::Unsat;
                }
                if self.trivially_unsat {
                    self.drat_emit_empty(None);
                    return SolverResult::Unsat;
                }
                if self.elim_finished {
                    break;
                }
            }
        }
        // Structured bounded variable addition (k-way common-literal-set
        // extraction): one-shot pre-search introduction of aux vars that
        // merge clause groups sharing a common part.  The encoding is
        // equisatisfiable AND model-preserving in both directions (see
        // `solver/bva.rs`), so no reconstruction record is needed.  Slice
        // gates inside the pass: level 0, base scope, no theory, no proof
        // tracer, bounded budgets.  Default off.
        if self.config.enable_sbva || std::env::var("OXIZ_SBVA").as_deref() == Ok("1") {
            let (added, saved) = self.structured_bva();
            if added > 0 {
                #[cfg(feature = "std")]
                eprintln!("c [bva] introduced={} literals_saved={}", added, saved);
            }
            if self.trivially_unsat {
                self.drat_emit_empty(None);
                return SolverResult::Unsat;
            }
        }
        // Equivalent-literal substitution (SCC on the binary implication graph).
        // Collapses binary-heavy formulas before search; a no-op (early-out)
        // when there are no non-trivial SCCs. Runs at level 0 / base scope only.
        if self.config.enable_equiv_substitution && !sched_parity {
            if self.substitute_equivalent_literals() == equiv::SubstOutcome::Unsat {
                self.drat_emit_empty(None);
                return SolverResult::Unsat;
            }
            if self.trivially_unsat {
                self.drat_emit_empty(None);
                return SolverResult::Unsat;
            }
        }
        // Forward subsumption + self-subsumption for callers that ran neither
        // elimination nor substitution (both of those already interleave their
        // own subsumption rounds). Skipped when equivalent-literal substitution
        // rewrote the clause database: the subsumption-after-substitution
        // sequence has a rare (≈1/15k) wrong-model interaction still under
        // investigation, so the two are not run together.
        if !self.config.enable_bve
            && !sched_parity
            && (self.config.enable_equiv_substitution || self.config.enable_inprocessing)
            && !self.did_equiv_subst
        {
            self.forward_subsumption();
            self.self_subsumption_pass();
            if self.trivially_unsat {
                self.drat_emit_empty(None);
                return SolverResult::Unsat;
            }
        }

        // Pre-search inprocessing pass (failed-literal probing + subsumption +
        // strengthening) when enabled. Mirrors cadical's preprocessing: for
        // structured instances (e.g. `longmult`) probing deduces forced units
        // up front. Probing runs once here (not on every periodic inprocess
        // call) because brute-force per-variable probing is too expensive to
        // repeat – cadical schedules it on binary-implication roots, which is a
        // larger follow-up.
        if self.config.enable_inprocessing && !sched_parity {
            if self.config.enable_failed_literal_probing {
                self.failed_literal_probing();
            }
            if !self.trivially_unsat && self.config.enable_hyper_binary_probing {
                self.probe_hyper_binary();
            }
            if !self.trivially_unsat {
                self.inprocess();
            }
            if !self.trivially_unsat {
                self.vivify_clauses();
            }
            if self.trivially_unsat {
                self.drat_emit_empty(None);
                return SolverResult::Unsat;
            }
        }

        // ===== CDCL search =====
        //
        // One search loop for every caller.  Historically `solve` carried its
        // own inlined copy of the CDCL loop while `solve_with_theory` carried
        // another, and the two drifted: the theory loop's `learn_clause` puts
        // binary learned clauses into the binary implication graph, picks the
        // second watch by `watch_rank` (not blindly index 1), and runs
        // on-the-fly subsumption on short low-glue clauses -- none of which the
        // inlined copy did.  On pure-SAT workloads that divergence measured
        // 5x: `mrpp_4x4#12_12` solved in 8.2s through `solve_with_theory`
        // with a no-op theory while the inlined `solve` loop needed >40s for
        // the identical clause set.  `solve` now runs its pre-search passes
        // and hands the search itself to [`Self::solve_with_theory`] with a
        // no-op callback, so the plain-SAT path can never again silently miss
        // an improvement landed on the CDCL(T) path (or vice versa).
        struct NoopTheory;
        impl TheoryCallback for NoopTheory {
            fn on_assignment(&mut self, _lit: Lit) -> TheoryCheckResult {
                TheoryCheckResult::Sat
            }
            fn final_check(&mut self) -> TheoryCheckResult {
                TheoryCheckResult::Sat
            }
            fn on_backtrack(&mut self, _level: u32) {}
        }
        self.solve_with_theory(&mut NoopTheory)
    }

    /// Solve with assumptions and return unsat core if UNSAT
    ///
    /// This is the key method for MaxSAT: it solves under assumptions and
    /// if the result is UNSAT, returns the subset of assumptions in the core.
    ///
    /// # Arguments
    /// * `assumptions` - Literals that must be true
    ///
    /// # Returns
    /// * `(SolverResult, Option<Vec<Lit>>)` - Result and unsat core (if UNSAT)
    pub fn solve_with_assumptions(
        &mut self,
        assumptions: &[Lit],
    ) -> (SolverResult, Option<Vec<Lit>>) {
        // Gatekeeper (SK-1): refuse to answer once a BVE-eliminated variable
        // was reintroduced (no sound way to honor it).
        if self.fatal_error.is_some() {
            return (SolverResult::Unknown, None);
        }
        // Rewrite any assumption literal naming an ELS-eliminated variable
        // through the substitution map (same sound fix as `add_clause`).
        let mut assumptions: Vec<Lit> = assumptions.to_vec();
        for l in assumptions.iter_mut() {
            *l = self.resolve_reintroduced_literal(*l);
        }
        let assumptions = assumptions.as_slice();
        // While this call is in flight, destructive inprocessing must not
        // fold assumption variables out of the search (cadical freezes
        // assumed variables). Cleared on every exit path below via the
        // epilogue helper.
        self.assumptions_active = true;
        let (res, core) = self.solve_with_assumptions_inner(assumptions);
        self.assumptions_active = false;
        (res, core)
    }

    fn solve_with_assumptions_inner(
        &mut self,
        assumptions: &[Lit],
    ) -> (SolverResult, Option<Vec<Lit>>) {
        if self.fatal_error.is_some() {
            return (SolverResult::Unknown, None);
        }
        if self.trivially_unsat {
            return (SolverResult::Unsat, Some(Vec::new()));
        }

        // Ensure all assumption variables exist
        for &lit in assumptions {
            while self.num_vars <= lit.var().index() {
                self.new_var();
            }
        }

        // A prior solve() may have returned Sat while leaving its full model on the
        // trail (decisions at levels > 0). Fully restart the search state by
        // backtracking to the root BEFORE capturing `assumption_level_start` and
        // testing the assumptions. Otherwise leftover model decisions masquerade as
        // fixed level-0 facts: an assumption that merely disagrees with the previous
        // arbitrary model would hit `value.is_false()` below and be reported as a
        // false UNSAT (e.g. (a∨b); solve() picks ¬a,b; then assumptions=[a] must be
        // SAT, not UNSAT). This is the standard incremental / MaxSAT entry protocol.
        self.backtrack_with_phase_saving(0);

        // Clear conflict-analysis marks so a stale `seen` array left by a previous
        // solve cannot pollute the extracted assumption core.
        for s in &mut self.seen {
            *s = false;
        }

        // Initial propagation at level 0
        if self.propagate().is_some() {
            return (SolverResult::Unsat, Some(Vec::new()));
        }

        // Create a new decision level for assumptions
        let assumption_level_start = self.trail.decision_level();

        // Assign assumptions as decisions
        for (i, &lit) in assumptions.iter().enumerate() {
            // Check if already assigned
            let value = self.trail.lit_value(lit);
            if value.is_true() {
                continue; // Already satisfied
            }
            if value.is_false() {
                // Conflict with assumption - extract core from conflicting assumptions
                let core = self.extract_assumption_core(assumptions, i);
                self.backtrack(assumption_level_start);
                return (SolverResult::Unsat, Some(core));
            }

            // Make decision for assumption
            self.trail.new_decision_level();
            self.trail.assign_decision(lit);

            // Propagate after each assumption
            if let Some(conflict) = self.propagate() {
                // Conflict during assumption propagation: collect the full set of
                // contributing assumptions from the conflict clause.
                let core = self.analyze_assumption_conflict(assumptions, conflict);
                self.backtrack(assumption_level_start);
                return (SolverResult::Unsat, Some(core));
            }
        }

        // Now solve normally
        loop {
            // Resource budget / interrupt check: abandon under-assumption search
            // and report Unknown when the conflict budget or interrupt fires.
            if self.should_stop_search() {
                self.backtrack(assumption_level_start);
                return (SolverResult::Unknown, None);
            }

            if let Some(conflict) = self.propagate() {
                self.debug_check_conflict_clause(conflict);
                self.stats.conflicts += 1;

                // Check if conflict involves assumptions
                let backtrack_level = self.analyze_conflict_level(conflict);

                if backtrack_level <= assumption_level_start {
                    // Conflict forces backtracking past assumptions - UNSAT
                    let core = self.analyze_assumption_conflict(assumptions, conflict);
                    self.backtrack(assumption_level_start);
                    return (SolverResult::Unsat, Some(core));
                }

                let (bt_level, learnt_clause) = self.analyze(conflict);

                // Empty learned clause = genuine root-level (level-0) refutation.
                // The `backtrack_level <= assumption_level_start` guard above
                // already routes all-level-0 conflicts to the UNSAT-core path, so
                // this is a belt-and-braces guard that also avoids an empty-clause
                // index panic in `learn_clause`.
                if learnt_clause.is_empty() {
                    let core = self.analyze_assumption_conflict(assumptions, conflict);
                    self.backtrack(assumption_level_start);
                    return (SolverResult::Unsat, Some(core));
                }

                self.backtrack_with_phase_saving(bt_level.max(assumption_level_start + 1));
                self.debug_check_invariants("after backtrack (assumptions)");
                self.learn_clause(learnt_clause);

                self.decay_vsids();
                self.decay_clause_activity();
                self.handle_clause_deletion_and_restart_limited(assumption_level_start);
            } else {
                // No conflict - try to decide. `propagate()` just returned `None`,
                // i.e. reached a fixpoint.
                self.debug_check_fixpoint_invariants("after propagation fixpoint (assumptions)");
                if let Some(var) = self.pick_branch_var() {
                    self.stats.decisions += 1;
                    self.trail.new_decision_level();

                    let polarity = self.decision_polarity(var);
                    let lit = if polarity {
                        Lit::pos(var)
                    } else {
                        Lit::neg(var)
                    };
                    self.trail.assign_decision(lit);
                } else {
                    // All variables assigned - SAT
                    self.save_model();
                    self.debug_verify_model();
                    self.debug_check_invariants("at SAT (assumptions)");
                    self.backtrack(assumption_level_start);
                    return (SolverResult::Sat, None);
                }
            }
        }
    }

    /// Retire a clause from the live database, first re-pointing any live
    /// trail-reason reference to `Decision`.
    ///
    /// **Every** in-solver deletion path must go through here (subsume,
    /// BVE/ELS preprocessing, the eliminator, probe case-(B)): a retired
    /// clause can be the recorded propagation reason of an assigned trail
    /// literal, and binary reasons escape the `lits[0]` invariant (the
    /// binary-graph propagation path records either position). A `Decision`
    /// reason is semantically exact for these cases – level-0 facts never
    /// enter conflict analysis (cadical: `v.reason = level ? … : 0`) – and
    /// the deleted-reason invariant stays intact. Found by the debug
    /// invariant via `Break_unsat_06_07` under `INPROCESS+PROBE+HBP+BVE`.
    /// `retire_clause` + counter/stat bookkeeping + binary-graph purge +
    /// DRAT deletion (the `ClauseDatabase::remove` shape) – use where the
    /// old code called `clauses.remove` directly on clauses that may be
    /// live reasons (the on-the-fly subsumption path).
    pub(super) fn remove_clause(&mut self, cid: ClauseId) {
        if let Some(v) = self.clauses.get(cid).filter(|c| !c.deleted) {
            let lits: SmallVec<[Lit; 8]> = v.lits.iter().copied().collect();
            for l in lits {
                let var = l.var();
                if self.trail.is_assigned(var)
                    && matches!(self.trail.reason(var), Reason::Propagation(r) if r == cid)
                {
                    self.trail.set_reason(var, Reason::Decision);
                }
            }
        }
        self.purge_binary_edges(cid);
        self.drat_delete(cid);
        self.clauses.remove(cid);
    }

    pub(super) fn retire_clause(&mut self, cid: ClauseId) {
        // Purge binary-graph edges FIRST (the purge reads the clause's
        // literals and requires the deleted flag to be clear): a stale edge
        // of a deleted binary keeps PROPAGATING (the binary loop does not
        // consult the deleted flag) and re-records reasons pointing at the
        // deleted clause — the exact re-establishment the debug invariant
        // caught on Break_unsat_06_07.
        self.purge_binary_edges(cid);
        if let Some(v) = self.clauses.get(cid).filter(|c| !c.deleted) {
            let lits: SmallVec<[Lit; 8]> = v.lits.iter().copied().collect();
            for l in lits {
                let var = l.var();
                if self.trail.is_assigned(var)
                    && matches!(self.trail.reason(var), Reason::Propagation(r) if r == cid)
                {
                    self.trail.set_reason(var, Reason::Decision);
                }
            }
        }
        self.clauses.mark_deleted_raw(cid);
    }

    /// Freeze the variables the caller's theory observes (see
    /// `Solver::frozen_vars`).  Must be called before the first `solve*`
    /// pre-search pass; later calls extend the set (idempotent).  After
    /// this, `Solver::elimination_allowed`-class gates treat destructive
    /// preprocessing as safe: the passes still refuse every frozen
    /// variable, so only Boolean-structure variables are touched.
    pub fn freeze_theory_vars<I: IntoIterator<Item = Var>>(&mut self, vars: I) {
        for v in vars {
            self.frozen_vars.insert(v);
        }
        self.theory_vars_frozen = true;
    }

    /// Get the model (if sat)
    #[must_use]
    pub fn model(&self) -> &[LBool] {
        &self.model
    }

    /// Get the value of a variable in the model
    #[must_use]
    pub fn model_value(&self, var: Var) -> LBool {
        self.model.get(var.index()).copied().unwrap_or(LBool::Undef)
    }

    /// Get statistics
    #[must_use]
    /// Search-state memory composition (diagnostics: `OXIZ_MEM_STATS` in
    /// the harnesses). Live bytes vs allocation slack for the structures
    /// that dominate long runs: the clause arena, the id→ref table, watch
    /// lists, and the binary implication graph. All are live-data
    /// footprints except the per-list Vec capacity overshoot columns.
    pub fn memory_composition(&self) -> MemoryComposition {
        let arena = self.clauses.arena_stats();
        let (big_edges, big_cap) = self.binary_graph.edge_accounting();
        let watch: (usize, usize) = self.watches.watcher_accounting();
        MemoryComposition {
            arena_used_bytes: arena.used_bytes,
            arena_capacity_bytes: arena.total_bytes,
            arena_wasted_bytes: arena.wasted_bytes,
            refs_bytes: self.clauses.num_slots() * 4,
            watch_bytes: watch.0 * core::mem::size_of::<crate::watched::Watcher>(),
            watch_capacity_bytes: watch.1 * core::mem::size_of::<crate::watched::Watcher>(),
            big_edge_bytes: big_edges * 8,
            big_capacity_bytes: big_cap * 8,
            arena_compactions: arena.compactions,
        }
    }

    /// Get solver statistics.
    pub fn stats(&self) -> &SolverStats {
        &self.stats
    }

    /// Number of completed stable/focused mode switches (cadical
    /// `stats.stabphases`). Diagnostic accessor for the search-shape studies.
    #[must_use]
    pub fn stabilization_phases(&self) -> u64 {
        self.stabphases
    }

    /// Total search ticks per mode (`ticks_focused`, `ticks_stable`).
    /// Diagnostic accessor for cross-solver schedule calibration.
    #[must_use]
    pub fn search_ticks(&self) -> (u64, u64) {
        (self.ticks_focused, self.ticks_stable)
    }

    /// Shrink-study accumulator (see `conflict.rs`; `OXIZ_SHRINK_TRACE=1`).
    #[must_use]
    pub fn shrink_trace_stats(&self) -> (u64, u64, u64, u64, u64, u64, u64, u64) {
        self.shrink_trace
    }

    /// Shrink-study failure-reason counters (debug instrumentation).
    #[must_use]
    /// Local-search walk counters (see `WalkCounters`).
    pub fn walk_counters(&self) -> WalkCounters {
        self.stats.walk
    }

    /// Shrink-study failure-reason counters (doc-hidden measurement API;
    /// see `OXIZ_SHRINK_TRACE` in `conflict.rs`).
    #[doc(hidden)]
    pub fn shrink_fail_stats(&self) -> (u64, u64, u64, u64, u64, u64, u64) {
        (
            self.shrink_fail_low,
            self.shrink_fail_above,
            self.mini_reject_no_reason,
            self.mini_reject_poison,
            self.mini_reject_conflict_level,
            self.mini_reject_knuth,
            self.mini_reject_early_abort,
        )
    }

    /// Get memory optimizer statistics
    #[must_use]
    pub fn memory_opt_stats(&self) -> &crate::memory_opt::MemoryOptStats {
        self.memory_optimizer.stats()
    }

    /// Get number of variables
    #[must_use]
    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    /// Switch the branching heuristic to pure VSIDS (disable VMTF and the
    /// cadical-style focused/stable dual mode).  Used for logic-gated
    /// configurations where VSIDS is the lever (e.g. QF_IDL/QF_UFIDL with
    /// bound propagation: VSIDS + arith-bound-prop closes the vhard family
    /// that the default VMTF-focused mode leaves open).  Must be called before
    /// search begins (from `set_logic`); a mid-search switch would leave the
    /// VMTF/LRB/CHB heaps stale, but `pick_branch_var` re-checks the flags on
    /// every decision so the VSIDS heap (kept warm by conflict bumping
    /// regardless of mode) is always current.
    /// Whether focused-mode VMTF scores are active (see `focused_vmtf`).
    #[must_use]
    pub fn is_focused_vmtf_enabled(&self) -> bool {
        self.config.focused_vmtf
    }

    /// Restore cadical focused-mode VMTF scores (undoing a CDCL(T)-level
    /// `focused_vmtf = false` posture) mid-setup, before any search starts.
    /// See the `focused_vmtf` field's docs.
    pub fn restore_focused_vmtf(&mut self) {
        self.config.focused_vmtf = true;
    }

    /// Force pure-VSIDS branching with no stable/focused schedule (legacy
    /// posture used by the difference-logic routing; see
    /// `route_branching_from_features`).
    pub fn set_branching_vsids(&mut self) {
        self.config.use_vmtf = false;
        self.config.use_lrb_branching = false;
        self.config.use_chb_branching = false;
        self.config.enable_stabilize = false;
    }

    /// Get number of clauses
    /// Soundness gate: does the current trail falsify a live clause?
    ///
    /// With a correct BCP this is never true – a clause whose every literal is
    /// false is a conflict, and `propagate` must have reported it before the
    /// search could run out of variables to assign.  It is checked anyway at the
    /// one place a wrong answer would escape (the `Sat` exit of the CDCL(T)
    /// loop), because a stale watch means `propagate` silently stops enforcing a
    /// clause: the search then assigns every variable, sees no conflict, and
    /// reports a "model" that violates the formula.
    ///
    /// Answering `Unknown` on such a trail is a backstop, not a repair; the
    /// underlying propagation defect still needs fixing.  Cost is one linear
    /// scan of the clause database, paid once per `Sat` verdict.
    ///
    /// Disabled once `push()` has been used: `pop()` leaves retracted clauses
    /// live in the database (watch lists are cleaned lazily), so the scan would
    /// flag them and turn a correct `Sat` into `Unknown`.
    #[must_use]
    pub fn trail_falsifies_live_clause(&self) -> bool {
        if self.ever_pushed {
            return false;
        }
        self.clauses.iter_ids().any(|id| {
            self.clauses.get(id).is_some_and(|c| {
                !c.deleted
                    && !c.lits.is_empty()
                    && c.lits.iter().all(|l| self.trail.lit_value(*l).is_false())
            })
        })
    }

    /// Total number of clauses currently in the database (original + learned).
    #[must_use]
    /// Total number of live clauses (original plus learned) in the database.
    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }

    /// Number of *original* (asserted, non-learned) clauses in the database.
    ///
    /// This is the ground truth for "how much did the caller's encoding grow",
    /// and it is **not** the same as `num_clauses() - learned_clause_count()`:
    /// [`Self::learned_clause_count`] reports the size of the
    /// `learned_clause_ids` registry, which is a *subset* of the clauses the
    /// database itself flags as learned (the registry exists so an incremental
    /// caller can forget a probe's learned clauses again).  Subtracting it from
    /// the total therefore silently counts every unregistered learned clause as
    /// "original".  Callers that want to pin encoder growth must use this.
    #[must_use]
    pub fn num_original_clauses(&self) -> usize {
        self.clauses.num_original()
    }

    /// Number of clauses the database flags as learned.
    ///
    /// See [`Self::num_original_clauses`] for why this can exceed
    /// [`Self::learned_clause_count`].
    #[must_use]
    pub fn num_learned_clauses(&self) -> usize {
        self.clauses.num_learned()
    }

    /// Push a new assertion level (for incremental solving)
    ///
    /// This saves the current state so that clauses added after this point
    /// can be removed with pop(). Automatically backtracks to decision level 0
    /// to ensure a clean state for adding new constraints.
    pub fn push(&mut self) {
        self.ever_pushed = true;
        // Backtrack to level 0 to ensure clean state
        // This is necessary because solve() may leave assignments on the trail
        // Use phase-saving backtrack to properly re-insert variables into decision heaps
        self.backtrack_with_phase_saving(0);

        self.assertion_levels.push(self.clauses.num_original());
        self.assertion_trail_sizes.push(self.trail.size());
        self.assertion_clause_ids.push(Vec::new());
    }

    /// Pop to previous assertion level
    pub fn pop(&mut self) {
        if self.assertion_levels.len() > 1 {
            self.assertion_levels.pop();

            // `trivially_unsat` records that the empty clause was derived
            // from LEVEL-0 facts alone.  Those facts are the current
            // assertion level's clauses, and this pop is removing some of
            // them, so the refutation no longer holds: keep the flag and a
            // later `(check-sat)` after the pop answers a wrong `unsat`
            // (the push/unsat/pop/check leak).  Clearing is always sound:
            // the worst case is re-deriving the same empty clause.
            self.trivially_unsat = false;

            // Get the trail size to backtrack to
            let trail_size = self.assertion_trail_sizes.pop().unwrap_or(0);

            // Remove all clauses added at this assertion level
            if let Some(clause_ids_to_remove) = self.assertion_clause_ids.pop() {
                for clause_id in clause_ids_to_remove {
                    // Purge any binary-implication-graph edges for this clause
                    // before removing it. Unlike the watch lists (which lazily
                    // skip deleted clauses during propagation), the binary graph
                    // is consulted directly, so leaving stale edges behind would
                    // let a retracted binary clause keep propagating after pop().
                    self.purge_binary_edges(clause_id);

                    // Record the retraction in the DRAT proof (if enabled) before
                    // the clause's literals become inaccessible.
                    self.drat_delete(clause_id);

                    // Remove from clause database
                    self.clauses.remove(clause_id);

                    // Remove from learned clause tracking if it's a learned clause
                    self.learned_clause_ids.retain(|&id| id != clause_id);

                    // Note: Watch lists will be cleaned up naturally during propagation
                    // as they check if clauses are deleted before using them
                }
            }

            // Backtrack trail to the exact size it was at push()
            // This properly handles unit clauses that were added after push
            // Note: backtrack_to_size clears values but doesn't re-insert into heaps,
            // so we need to manually re-insert unassigned variables.
            let current_size = self.trail.size();
            if current_size > trail_size {
                // Collect variables that will be unassigned
                let mut unassigned_vars = Vec::new();
                for i in trail_size..current_size {
                    let lit = self.trail.assignments()[i];
                    unassigned_vars.push(lit.var());
                }

                // Drop the lazy theory-propagation explanations of every
                // literal the pop unassigns: they justify assignments this
                // scope introduced, and a later check re-derives fresh ones.
                // A surviving entry for an unassigned var would resolve a
                // FUTURE conflict against antecedents whose truth depended
                // on the popped scope (false unsat across check/pop/check).
                for var in &unassigned_vars {
                    self.theory_prop_reasons.remove(var);
                }

                self.trail.backtrack_to_size(trail_size);
                // The conflict-free prefix cannot reach past the surviving
                // trail (same clamp every solver backtrack applies).
                self.no_conflict_until = self.no_conflict_until.min(trail_size);

                // Re-insert unassigned variables into decision heaps
                for var in unassigned_vars {
                    if !self.vsids.contains(var) {
                        self.vsids.insert(var);
                    }
                    if !self.chb.contains(var) {
                        self.chb.insert(var);
                    }
                    self.lrb.unassign(var);
                }
            }

            // Ensure we're at decision level 0 with proper heap re-insertion
            self.backtrack_with_phase_saving(0);

            // Re-arm unit propagation over the retained prefix.
            //
            // `backtrack_to_size` parks the propagation head at the end of the
            // surviving trail, declaring that prefix fully propagated. That is
            // false here for two independent reasons: the discarded suffix held
            // level-0 *consequences* of the retained prefix, and this pop has
            // just removed clauses the prefix was propagated against. The
            // surviving literals are therefore assigned but no longer followed by
            // their implications, and nothing would ever recompute them –
            // `backtrack_with_phase_saving(0)` above only clamps the head when it
            // actually rolls a level back, and after `backtrack_to_size` the
            // solver already sits at level 0.
            //
            // A clause left falsified that way is never revisited: its watched
            // literals were assigned before the head and so are never
            // re-propagated, so the conflict is silently lost and the next
            // `solve()` reports `Sat` on a model violating it. Rewinding costs
            // one extra pass over the retained watch lists; re-propagating an
            // already-assigned literal is a no-op, so it has no semantic effect
            // beyond restoring the facts the pop erased. Mirrors the same rewind
            // in `Solver::restore_to_trail_size`.
            self.trail.reset_propagation_head();

            // Clear the trivially_unsat flag as we've removed problematic clauses
            self.trivially_unsat = false;
        }
    }

    /// Backtrack to decision level 0 (for AllSAT enumeration)
    ///
    /// This is necessary after a SAT result before adding blocking clauses
    /// to ensure the new clauses can trigger propagation correctly.
    /// Uses phase-saving backtrack to properly re-insert unassigned variables
    /// into the decision heaps (VSIDS, CHB, LRB).
    pub fn backtrack_to_root(&mut self) {
        self.backtrack_with_phase_saving(0);
    }

    /// Reset the solver
    pub fn reset(&mut self) {
        self.clauses = ClauseDatabase::new();
        self.trail.clear();
        // The trail is empty now, so no `Reason::Theory` assignment is
        // observable; drop the lazy explanations with it.
        self.theory_prop_reasons.clear();
        self.theory_reason_clauses = 0;
        self.watches.clear();
        self.vsids.clear();
        self.domain_priority.clear();
        self.chb.clear();
        self.stats = SolverStats::default();
        self.learnt.clear();
        self.seen.clear();
        self.analyze_stack.clear();
        self.assertion_levels.clear();
        self.assertion_levels.push(0);
        self.assertion_trail_sizes.clear();
        self.assertion_trail_sizes.push(0);
        self.assertion_clause_ids.clear();
        self.assertion_clause_ids.push(Vec::new());
        self.model.clear();
        self.num_vars = 0;
        // Decision heuristics: `vsids`/`chb` are cleared below, but `vmtf`
        // and `lrb` only ever *grow* (`resize` is a no-op when num_vars shrinks),
        // so without resetting them they keep every variable from the pre-reset
        // problem as a live decision candidate.  Reusing the solver then lets
        // `pick_branch_var` return a variable index that no longer exists
        // (`num_vars` was reset to 0 and only the new problem's vars were
        // re-created via `new_var`), which `assign_decision` happily pushes onto
        // the trail – and the next `propagate` indexes the still-small
        // `binary_graph` (and other var-indexed arrays) out of bounds.
        // Rebuild them empty so `new_var` repopulates from scratch.
        self.vmtf = VMTF::new(0);
        self.lrb = LRB::new(0);
        self.best_phase.clear();
        self.target_phase.clear();
        self.target_assigned = 0;
        self.best_assigned = 0;
        self.no_conflict_until = 0;
        self.rephased = None;
        self.last_rephase_conflicts = 0;
        self.lim_rephase = 0;
        self.rephase_rounds = [0, 0];
        self.last_walk_ticks = 0;
        // `ever_pushed` latches once push/pop is used and permanently disables
        // the `trail_falsifies_live_clause` backstop.  It must be cleared on
        // reset so a fresh problem gets the backstop again.
        self.ever_pushed = false;
        self.restart_threshold = self.config.restart_interval;
        self.trivially_unsat = false;
        self.phase.clear();
        self.deterministic_phase.clear();
        self.luby_index = 0;
        self.level_marks.clear();
        self.lbd_mark = 0;
        self.learned_clause_ids.clear();
        self.conflicts_since_deletion = 0;
        self.rng_state = self.rng_seed;
        self.recent_lbd_sum = 0;
        self.recent_lbd_count = 0;
        self.binary_graph.clear();
        self.global_lbd_sum = 0;
        self.global_lbd_count = 0;
        self.conflicts_since_local_restart = 0;
        self.pure_literal_reconstruction.clear();
        // Drop any proof logger: its clause ids refer to the now-cleared database,
        // so continuing to emit against it would produce a meaningless proof.
        self.disable_proof();
    }

    /// Get the current trail (for theory solvers)
    #[must_use]
    pub fn trail(&self) -> &Trail {
        &self.trail
    }

    /// Get the current decision level
    #[must_use]
    pub fn decision_level(&self) -> u32 {
        self.trail.decision_level()
    }

    /// Debug method: print all learned clauses
    pub fn debug_print_learned_clauses(&self) {
        println!(
            "=== Learned Clauses ({}) ===",
            self.learned_clause_ids.len()
        );
        for (i, &cid) in self.learned_clause_ids.iter().enumerate() {
            if let Some(clause) = self.clauses.get(cid)
                && !clause.deleted
            {
                let lits: Vec<String> = clause
                    .lits
                    .iter()
                    .map(|lit| {
                        let var = lit.var().index();
                        if lit.is_pos() {
                            format!("v{}", var)
                        } else {
                            format!("~v{}", var)
                        }
                    })
                    .collect();
                println!(
                    "  Learned {}: ({}), LBD={}",
                    i,
                    lits.join(" | "),
                    clause.lbd
                );
            }
        }
    }

    /// Debug method: print binary implication graph entries
    pub fn debug_print_binary_graph(&self) {
        println!("=== Binary Implication Graph ===");
        for lit_code in 0..(self.num_vars * 2) {
            let lit = Lit::from_code(lit_code as u32);
            let implications = self.binary_graph.get(lit);
            if !implications.is_empty() {
                let lit_str = if lit.is_pos() {
                    format!("v{}", lit.var().index())
                } else {
                    format!("~v{}", lit.var().index())
                };
                for &(implied, _cid) in implications {
                    let impl_str = if implied.is_pos() {
                        format!("v{}", implied.var().index())
                    } else {
                        format!("~v{}", implied.var().index())
                    };
                    println!("  {} -> {}", lit_str, impl_str);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests;
