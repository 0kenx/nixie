//! OxiZ SAT Solver - High-performance CDCL SAT solver
//!
//! This crate implements a Conflict-Driven Clause Learning (CDCL) SAT solver
//! with the following features:
//! - Two-watched literals scheme for efficient unit propagation
//! - Multiple branching heuristics (VSIDS, LRB, CHB, VMTF)
//! - Clause learning with first-UIP scheme and recursive minimization
//! - Preprocessing (BCE, BVE, subsumption elimination)
//! - Incremental solving (push/pop)
//! - DRAT/LRAT proof logging, fully wired into the CDCL search (including
//!   recursive clause minimization with RUP-chain extension). Enable with
//!   [`Solver::enable_drat_proof`] / [`Solver::enable_lrat_proof`] (text or
//!   binary) *before* adding clauses; `solve()` then streams a checkable proof
//!   – derived clauses with RUP hint chains assembled during 1-UIP conflict
//!   analysis (and extended per minimized literal), id-based deletions, and the
//!   empty clause on UNSAT. Level-0 propagations are flushed to explicit
//!   derived units so the chain invariant holds. The LRAT proof is verified by
//!   `lrat-check` (vendored under `tools/`). See the `proof` module for the
//!   tracer/dispatcher architecture (faithful port of cadical's
//!   `Proof`/`Tracer`).
//! - Local search integration
//! - Parallel portfolio solving
//! - AllSAT enumeration
//!
//! # Threading and cancellation model
//!
//! The search core is deliberately **single-threaded**, matching CaDiCaL
//! (see `cadical.cpp`: the parallelism that exists – `parallel/`,
//! `portfolio` – drives *independent* `Solver` instances share-nothing and
//! is layered on top of this contract, not inside it).
//!
//! * **Reentrant across instances.** A [`Solver`] owns all of its state
//!   (trail, clause arena, heuristics, proof streams). The crate carries no
//!   mutable global state – its only static is a write-once `OnceLock<bool>`
//!   caching the `OXIZ_TRACE_DECISIONS` environment probe – so separate
//!   `Solver` objects may be constructed and solved from different threads
//!   concurrently, including in an external portfolio. This is pinned by
//!   `tests/threading_model.rs`.
//! * **Not safe for concurrent use of one instance.** Every mutating entry
//!   point takes `&mut self`, so the compiler rejects concurrent use of a
//!   single `Solver`; the standalone `oxiz` CLI additionally uses process-
//!   level machinery (signal handlers, timeout supervision) and, like
//!   CaDiCaL's `App`, is neither thread-safe nor reentrant.
//! * **Asynchronous termination is cooperative cancellation, not parallel
//!   solving.** [`Solver::set_interrupt`] attaches a caller-owned
//!   `Arc<AtomicBool>`; another thread may set it to `true` at any moment,
//!   and the current `solve*` call abandons the search and returns
//!   [`SolverResult::Unknown`] – never a wrong verdict, and the instance
//!   remains usable once the caller clears the flag. The flag is checked at
//!   the pre-search entry gate and at the top of every CDCL loop iteration;
//!   preprocessing passes are propagation-budgeted, so cancellation latency
//!   is bounded. The flag is **caller-owned**: clearing it between `solve`
//!   calls is the caller's responsibility (CaDiCaL's `Terminator` has the
//!   same semantics).
//!
//! # Examples
//!
//! ## Basic SAT Solving
//!
//! ```
//! use oxiz_sat::{Solver, SolverResult, Lit};
//!
//! let mut solver = Solver::new();
//!
//! // Create variables
//! let a = solver.new_var();
//! let b = solver.new_var();
//! let c = solver.new_var();
//!
//! // Add clause: a OR b
//! solver.add_clause([Lit::pos(a), Lit::pos(b)]);
//!
//! // Add clause: NOT a OR c
//! solver.add_clause([Lit::neg(a), Lit::pos(c)]);
//!
//! // Add clause: NOT b OR NOT c
//! solver.add_clause([Lit::neg(b), Lit::neg(c)]);
//!
//! match solver.solve() {
//!     SolverResult::Sat => println!("Satisfiable!"),
//!     SolverResult::Unsat => println!("Unsatisfiable!"),
//!     SolverResult::Unknown => println!("Unknown"),
//! }
//! ```
//!
//! ## Solving with Assumptions
//!
//! ```
//! use oxiz_sat::{Solver, SolverResult, Lit};
//!
//! let mut solver = Solver::new();
//! let a = solver.new_var();
//! let b = solver.new_var();
//!
//! solver.add_clause([Lit::pos(a), Lit::pos(b)]);
//!
//! // Solve assuming a is false
//! let (result, _) = solver.solve_with_assumptions(&[Lit::neg(a)]);
//! assert_eq!(result, SolverResult::Sat); // b must be true
//! ```

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), allow(unused_variables))]
#![deny(unsafe_code)]
#![warn(missing_docs)]

// Native builds must never silently end up on oxiz-time's frozen stub clock
// (the `std` feature forward in this crate's manifest is what selects the real
// one; see oxiz-time/src/lib.rs).
const _: () = assert!(!oxiz_time::IS_FROZEN);

#[cfg(not(feature = "std"))]
extern crate alloc;

mod prelude;

// ======== Always-available modules (no_std compatible) ========
mod activity;
mod agility;
mod allsat;
mod assumptions;
mod asymmetric_branching;
mod autotuning;
mod backbone;
mod big;
mod cardinality;
mod cce;
mod chb;
mod chrono;
mod chronological_backtrack;
mod clause;
mod clause_maintenance;
pub mod clause_pool;
mod clause_size_manager;
mod community;
mod community_partition;
mod config_presets;
mod cube;
mod distillation;
#[cfg(feature = "std")]
mod drat_inprocessing;
mod dynamic_lbd;
mod dynamic_subsumption;
mod els;
mod extended_resolution;
mod gate;
mod hyper_binary;
// Debug-net checkers: every production caller sits behind
// `#[cfg(debug_assertions)]` (see `Solver::debug_check_invariants`), so a
// release *lib* build has no callers and the module would be pure dead code
// there. Test builds keep it in both profiles – the invariant tests and the
// solver tests call the checkers directly.
#[cfg(any(debug_assertions, test))]
mod invariants;
mod literal;
mod lookahead;
mod lrb;
mod maxsat;
mod memory;
mod memory_opt;
mod ml_branching;
mod occurrence;
pub mod preprocessing;
mod preprocessing_core;
mod recursive_minimization;
mod reluctant;
mod resolution_graph;
mod restart_model;
mod smoothed_lbd;
mod solver;
mod stabilization;
mod subsumption;
mod symmetry;
#[cfg(feature = "std")]
pub mod tactics;
mod trail;
mod trail_saving;
mod uip_strategies;
mod unsat_core;
mod vivification;
mod vmtf;
mod vmtf_queue;
mod vsids;
mod watched;
mod xor;

// ======== std-only modules ========
#[cfg(feature = "std")]
mod benchmark;
#[cfg(feature = "std")]
mod clause_exchange;
#[cfg(feature = "std")]
mod cube_solver;
#[cfg(feature = "std")]
mod dimacs;
#[cfg(feature = "std")]
pub mod parallel;
#[cfg(feature = "std")]
mod portfolio;
#[cfg(feature = "profiling")]
pub mod profiling;
#[cfg(feature = "std")]
mod proof;
#[cfg(feature = "std")]
mod stats_dashboard;

// ======== Always-available exports ========
pub use activity::{ActivityStats, ClauseActivityManager, VariableActivityManager};
pub use agility::{AgilityStats, AgilityTracker};
pub use allsat::{AllSatEnumerator, EnumerationConfig, EnumerationResult, EnumerationStats, Model};
pub use assumptions::{
    Assumption, AssumptionContext, AssumptionCoreMinimizer, AssumptionLevel, AssumptionStack,
    AssumptionStats,
};
pub use asymmetric_branching::{AsymmetricBranching, AsymmetricBranchingStats};
pub use autotuning::{
    Autotuner, AutotuningStats, Configuration, Parameter,
    PerformanceMetrics as TuningPerformanceMetrics, TuningStrategy,
};
pub use backbone::{BackboneAlgorithm, BackboneDetector, BackboneFilter, BackboneStats};
pub use big::{BigStats, BinaryImplicationGraph};
pub use cardinality::CardinalityEncoder;
pub use cce::{CceStats, CoveredClauseElimination};
pub use chronological_backtrack::{
    BacktrackDecision, ChronoBacktrackConfig, ChronoBacktrackEngine, ChronoBacktrackStats,
};
/// Matched-null switch for the probe-ranking experiment (see
/// `docs/studies/`): cached env probe, read once per process.
#[doc(hidden)]
pub fn probe_null_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("OXIZ_PROBE_NULL").is_ok_and(|v| !v.is_empty() && v != "0"))
}

/// Opt-OUT for the root-sweep's retire half (cadical `collect.cpp`'s
/// satisfied-clause retirement at reduce time, permanence-guarded):
/// DEFAULT ON since the pass-8/9 root-cause work. `OXIZ_ROOT_SWEEP=0`
/// restores the pre-sweep behavior for A/B.
#[doc(hidden)]
pub fn root_sweep_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("OXIZ_ROOT_SWEEP").map_or(true, |v| v != "0"))
}

/// Sub-knob for the root sweep's STRIP half (falsified-literal removal):
/// `OXIZ_ROOT_SWEEP_STRIP=1`, default OFF - it answered wrong `unsat` on
/// two SAT corpus files (see the study); only its g2-slp win is behind it.
#[doc(hidden)]
pub fn root_sweep_strip_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("OXIZ_ROOT_SWEEP_STRIP").is_ok_and(|v| !v.is_empty() && v != "0")
    })
}

/// A/B switch for the walk-objective fixed-literal study (see the
/// zero-broken section of `docs/studies/2026-08-30-analyze-quadratics.md`):
/// when set, the walk's objective strips fixed-false literals from
/// participating clauses instead of excluding those clauses (cadical
/// walk-objective parity after garbage collection).  Default OFF – the
/// multi-seed verdict was chaos-shaped with deep regressions.
#[doc(hidden)]
pub fn walk_strip_fixed_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("OXIZ_WALK_STRIP_FIXED").is_ok_and(|v| !v.is_empty() && v != "0")
    })
}

/// Matched-null switch for the analysis-walk-glue restart-EMA experiment
/// (see `docs/studies/`): when set, the restart EMAs receive the *previous*
/// conflict's walk glue instead of the current one – same distribution,
/// same timing, no current-conflict information.
#[doc(hidden)]
pub fn glue_null_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("OXIZ_GLUE_NULL").is_ok_and(|v| !v.is_empty() && v != "0"))
}

/// A/B switch for the walk-glue restart-EMA port: when set, the EMAs keep
/// receiving the pre-port input (the stored clause's LBD).  Used by the seed
/// study to attribute the restart-cadence effect (see `docs/studies/`).
#[doc(hidden)]
pub fn glue_legacy_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("OXIZ_GLUE_LEGACY").is_ok_and(|v| !v.is_empty() && v != "0"))
}

/// Matched-null switch for the chronological trail-reuse port: when set,
/// the best-variable scan over the discarded region uses a scrambled bump
/// key (same scan, same work, no selection semantics).
#[doc(hidden)]
pub fn chrono_reuse_null_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("OXIZ_CHRONOREUSE_NULL").is_ok_and(|v| !v.is_empty() && v != "0")
    })
}

/// Matched-null switch for the clause-shrinking experiment (see
/// `docs/studies/`): when set, the full shrink walk runs (same work, same
/// side effects) but its result is discarded and the plain recursive
/// minimizer produces the stored clause – isolating the semantic content of
/// block-UIP shrinking from its cost and trajectory reshuffling.
/// Reduce used-shield (cadical `reduce.cpp` parity port): shield
/// recently-used learned clauses from tier-percentage deletion.
/// **Default OFF** — corpus-negative in screening (23 vs 25 solved on a
/// 60-file satcomp sample, 0 verdict mismatches; our tier promotions
/// already reward use, so the shield over-retains under the
/// tier-percentage policy).  `OXIZ_REDUCE_USED_SHIELD=1` enables for A/B
/// (see the standing-gap study's reduction-anomaly section).
#[doc(hidden)]
pub fn reduce_used_shield_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("OXIZ_REDUCE_USED_SHIELD").is_ok_and(|v| v != "0"))
}

/// Cached `OXIZ_VIVIFY_OTF=0` (disable on-the-fly vivify subsumption).
/// OnceLock: this is checked per subsumption candidate during vivify
/// rounds — an uncached `env::var` there measured as double-digit
/// percentages of runtime in `getenv` (profiled 2026-08-21, noL).
#[doc(hidden)]
pub fn vivify_otf_disabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("OXIZ_VIVIFY_OTF").as_deref() == Ok("0"))
}

/// Cached `OXIZ_VIVIFY_TRACE` (per-round vivify diagnostics print).
#[doc(hidden)]
pub fn vivify_trace_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("OXIZ_VIVIFY_TRACE").is_ok())
}

/// Cached `OXIZ_NOPROMOTE` (keep learned clauses out of original-slot
/// promotion).  Checked per learned-clause subsumption event.
#[doc(hidden)]
pub fn nopromote_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("OXIZ_NOPROMOTE").is_ok())
}

#[doc(hidden)]
pub fn shrink_null_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("OXIZ_SHRINK_NULL").is_ok_and(|v| !v.is_empty() && v != "0"))
}

/// Treatment switch for the cadical `bump_variable` mode-gating port (see
/// `docs/studies/2026-08-sat-mode-gated-bumping.md`): when set, conflict
/// bumps reach only the *active* mode's decision structure – scores
/// (VSIDS/EVSIDS) in stable mode, the VMTF queue in focused mode – exactly
/// like `Internal::bump_variable`'s `if (use_scores ())` split. The default
/// (unset) keeps the historical double-maintenance: both structures are
/// bumped on every conflict regardless of mode.
#[doc(hidden)]
pub fn bump_mode_gate_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("OXIZ_BUMP_MODE_GATE").is_ok_and(|v| !v.is_empty() && v != "0")
    })
}

/// Matched null for [`bump_mode_gate_enabled`]: same structural change (the
/// inactive structure stops receiving the analyzed variables), but in stable
/// mode the score bumps go to a **randomly chosen** variable set of the same
/// size instead of the conflict-analyzed ones – identical work, identical
/// perturbation, no signal. Focused-mode behavior matches the treatment
/// (queue-only). If treatment beats this null, the win is attributable to
/// delivering the real analysis signal through one structure, not to the
/// removal of double-maintenance overhead or to trajectory reshuffling.
#[doc(hidden)]
pub fn bump_mode_gate_null_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("OXIZ_BUMP_MODE_GATE_NULL").is_ok_and(|v| !v.is_empty() && v != "0")
    })
}

/// Treatment switch for the cadical `reduce.cpp` port (see
/// `docs/studies/2026-08-sat-cadical-reduce.md`): schedule-driven clause-database
/// reduction (first at conflict 300, then `reduceint * sqrt(conflicts)`
/// apart) with glue/used-tiered retention, replacing the fixed-12000-conflict
/// tier-percentage reduce.
#[doc(hidden)]
pub fn cadical_reduce_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("OXIZ_CADICAL_REDUCE").is_ok_and(|v| !v.is_empty() && v != "0")
    })
}

/// Matched null for [`cadical_reduce_enabled`]: identical trigger schedule
/// and identical deletion counts, but the clauses to delete are drawn
/// uniformly at random instead of by glue/size/used ranking – same
/// perturbation, no retention semantics.
#[doc(hidden)]
pub fn cadical_reduce_null_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("OXIZ_CADICAL_REDUCE_NULL").is_ok_and(|v| !v.is_empty() && v != "0")
    })
}

/// Clause-arena compaction (standing-gap lever 1,
/// `docs/studies/2026-09-01-standing-vs-kissat-gap-decomposition.md`):
/// ON by default. `OXIZ_NO_ARENA_COMPACT=1` disables – the A/B switch for
/// measuring the reclamation (the operation is trajectory-neutral by
/// construction, so no matched null is needed; the switch exists for RSS
/// before/after and emergency use).
#[doc(hidden)]
pub fn arena_compact_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| {
        !std::env::var("OXIZ_NO_ARENA_COMPACT").is_ok_and(|v| !v.is_empty() && v != "0")
    })
}

/// Treatment switch for the cadical `stabilizing ()` schedule port (see
/// `docs/studies/2026-08-sat-stabilize-schedule.md`): the first
/// focused/stable switch fires at `stabilizeinit` (1000) **conflicts**; the
/// increment is then *measured* as phase 1's consumed ticks, and each later
/// phase lasts `inc x stabphases^2` ticks. Replaces the historical fixed
/// `stabilize_base`-ticks schedule whose quadratic constant never adapts.
#[doc(hidden)]
pub fn stab_faithful_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("OXIZ_STAB_FAITHFUL").is_ok_and(|v| !v.is_empty() && v != "0")
    })
}

/// Matched null for [`stab_faithful_enabled`]: identical set of phase lengths
/// (the same `inc x k^2` values), applied in a pseudo-randomly shuffled order
/// – same perturbation magnitude and phase-count distribution, no monotone
/// growth semantics.
#[doc(hidden)]
pub fn stab_null_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("OXIZ_STAB_NULL").is_ok_and(|v| !v.is_empty() && v != "0"))
}

/// Diagnostics (`OXIZ_REASON_STATS`): BCP propagation counts split by whether
/// the reason clause was learned or original. Process-global atomics so the
/// stats harness can read them after `solve()`; diagnostic-only.
#[doc(hidden)]
pub static DIAG_REASON_LEARNED: core::sync::atomic::AtomicU64 =
    core::sync::atomic::AtomicU64::new(0);
#[doc(hidden)]
pub static DIAG_REASON_ORIGINAL: core::sync::atomic::AtomicU64 =
    core::sync::atomic::AtomicU64::new(0);
/// Diagnostics (`OXIZ_VMTF_SCAN=1` arms the counter): total linked-list steps
/// walked by `VMTF::next_decision` picks. Divide by decision count for the
/// mean scan length per decision – a growing value indicates search-pointer
/// stagnation.
#[doc(hidden)]
pub static DIAG_VMTF_SCAN: core::sync::atomic::AtomicU64 = core::sync::atomic::AtomicU64::new(0);

/// Gate for [`DIAG_VMTF_SCAN`] accumulation (`OXIZ_VMTF_SCAN=1`).
#[doc(hidden)]
pub fn vmtf_scan_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("OXIZ_VMTF_SCAN").is_ok_and(|v| !v.is_empty() && v != "0"))
}

pub use clause::{Clause, ClauseDatabase, ClauseDatabaseStats, ClauseId, ClauseTier};
pub use clause_maintenance::{ClauseMaintenance, MaintenanceStats};
pub use clause_size_manager::{ClauseSizeManager, SizeAdjustmentStrategy, SizeManagerStats};
pub use community::{
    Communities, CommunityOrdering, CommunityStats, LouvainDetector, VariableIncidenceGraph,
};
pub use community_partition::{CommunityPartition, PartitionStats};
pub use config_presets::ConfigPreset;
pub use cube::{Cube, CubeConfig, CubeGenerator, CubeResult, CubeSplittingStrategy, CubeStats};
pub use distillation::{Distillation, DistillationStats};
#[cfg(feature = "std")]
pub use drat_inprocessing::{DratInprocessingConfig, DratInprocessingStats, DratInprocessor};
pub use dynamic_lbd::{DynamicLbdManager, DynamicLbdStats};
pub use dynamic_subsumption::{
    DynamicSubsumption, SubsumptionConfig as DynamicSubsumptionConfig, SubsumptionResult,
    SubsumptionStats as DynamicSubsumptionStats,
};
pub use els::{ElsStats, EquivalentLiteralSubstitution};
pub use extended_resolution::{ClauseSubstitution, ExtendedResolution, Extension, ExtensionType};
pub use gate::{GateDetector, GateStats, GateType};
pub use hyper_binary::{HbrResult, HyperBinaryResolver, HyperBinaryStats};
pub use literal::{LBool, Lit, Var};
pub use lookahead::{LookaheadBranching, LookaheadHeuristic, LookaheadStats};
pub use maxsat::{MaxSatClause, MaxSatConfig, MaxSatResult, MaxSatSolver, MaxSatStats, Weight};
pub use memory::{ClauseArena, ClauseRef, MemoryStats};
pub use memory_opt::{MemoryAction, MemoryOptStats, MemoryOptimizer, SizeClass};
pub use ml_branching::{MLBranching, MLBranchingConfig, MLBranchingStats};
pub use occurrence::{OccurrenceList, OccurrenceStats};
pub use preprocessing_core::Preprocessor;
pub use recursive_minimization::{RecursiveMinStats, RecursiveMinimizer};
pub use reluctant::{ReluctantDoubling, ReluctantStats};
pub use resolution_graph::{
    GraphStats as ResolutionGraphStats, ResolutionAnalyzer, ResolutionGraph, ResolutionNode,
};
pub use smoothed_lbd::{SmoothedLbdStats, SmoothedLbdTracker};
pub use solver::{
    BoxedBranchingHeuristic, BranchingHeuristic, RestartStrategy, Solver, SolverConfig,
    SolverError, SolverResult, SolverStats, TheoryCallback, TheoryCheckResult,
};
pub use stabilization::{
    SearchMode, StabilizationConfig, StabilizationManager, StabilizationStats,
};
pub use subsumption::{SubsumptionChecker, SubsumptionStats};
pub use symmetry::{
    AutomorphismDetector, MatrixSymmetry, Permutation, SymmetryBreaker, SymmetryBreakingMethod,
    SymmetryGroup,
};
#[cfg(feature = "std")]
pub use tactics::{CubeImproveTactic, SymmetryBreakTactic};
pub use trail::{Reason, Trail};
pub use trail_saving::{SavedTrail, TrailSavingManager, TrailSavingStats};
pub use uip_strategies::{UipAnalysisResult, UipAnalyzer, UipConfig, UipStats, UipStrategy};
pub use unsat_core::UnsatCore;
pub use vivification::{Vivification, VivificationStats};
pub use vmtf::{VMTF, VmtfStats};
pub use vmtf_queue::{VmtfBumpQueue, VmtfBumpStats};
pub use xor::{
    GF2Matrix, GF2Row, PropagateResult, XorAddResult, XorClause, XorClauseId, XorConstraint,
    XorDetector, XorManager, XorPropagator, XorPropagatorStats, XorStrengthening, XorSubsumption,
};

// ======== std-only exports ========
#[cfg(feature = "std")]
pub use benchmark::{BenchmarkHarness, BenchmarkResult};
#[cfg(feature = "std")]
pub use clause_exchange::{ClauseExchangeBuffer, ExchangeConfig, ExchangeStats, SharedClause};
#[cfg(feature = "std")]
pub use cube_solver::{
    CubeAndConquer, CubeSolveResult, CubeSolverConfig, CubeSolverStats, ParallelCubeSolver,
};
#[cfg(feature = "std")]
pub use dimacs::{DimacsError, DimacsParser, DimacsWriter};
#[cfg(feature = "std")]
pub use parallel::{
    ParallelClauseSimplifier, ParallelProofChecker, PortfolioConfig as ParallelPortfolioConfig,
    PortfolioResult as ParallelPortfolioResult, PortfolioSolver as ParallelPortfolioSolver,
    ProofCheckConfig, ProofCheckResult, SimplificationConfig, SimplificationResult, SolverVariant,
};
#[cfg(feature = "std")]
pub use portfolio::{PortfolioConfig, PortfolioResult, PortfolioSolver, PortfolioStats};
#[cfg(feature = "profiling")]
pub use profiling::{
    ProfilingCategory, ProfilingCategorySnapshot, ProfilingSnapshot, ProfilingStats, ScopedTimer,
};
#[cfg(feature = "std")]
pub use proof::{
    ConclusionType, DratTracer, DratWriter, LratTracer, LratTranscript, LratTranscriptHandle,
    LratWriter, MemoryLratTracer, Proof, ProofTrimmer, Tracer,
};
#[cfg(feature = "std")]
pub use stats_dashboard::{StatsAggregator, StatsDashboard};
