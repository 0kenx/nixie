//! Solver configuration: [`SolverConfig`], its [`Default`] impl, and
//! [`RestartStrategy`]. Split out of `solver/mod.rs` to keep that file under
//! the project's line-count limit as the inprocessing toolkit
//! (`enable_failed_literal_probing`/`enable_bve`/`enable_equiv_substitution`/
//! `enable_gate_congruence`) grew the struct; re-exported from `solver/mod.rs`
//! so `oxiz_sat::SolverConfig`/`oxiz_sat::RestartStrategy` are unaffected.

use super::*;

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
    /// Inprocessing interval (number of conflicts between inprocessing)
    pub inprocessing_interval: u64,
    /// Enable chronological backtracking
    pub enable_chronological_backtrack: bool,
    /// Chronological backtracking threshold (max distance from assertion level)
    pub chrono_backtrack_threshold: u32,
    /// Use the VMTF move-to-front queue instead of VSIDS for decisions while
    /// the search is in *focused* mode (see [`SolverConfig::enable_stabilize`]).
    /// While in *stable* mode — or always, when `enable_stabilize` is off —
    /// VSIDS is used. Ignored when `use_chb_branching`/`use_lrb_branching`
    /// select a different heuristic outright.
    pub use_vmtf: bool,
    /// Cap on the Luby restart multiplier so the sequence's `2^k` growth
    /// cannot inflate the restart interval into a multi-thousand-conflict
    /// grind on long runs. `0` means uncapped. Only consulted by
    /// [`RestartStrategy::Luby`] when [`SolverConfig::enable_stabilize`] is
    /// off; the stable/focused schedule uses [`SolverConfig::focused_luby_cap`]
    /// instead.
    pub luby_cap: u64,
    /// Enable the stable/focused restart schedule: alternate a *focused*
    /// phase (frequent Glucose-EMA-triggered restarts, capped Luby length)
    /// with a *stable* phase (rare reluctant-doubling restarts, eligible for
    /// rephasing) on a quadratically-growing tick budget per phase. Off
    /// falls back to the legacy single restart strategy selected by
    /// [`SolverConfig::restart_strategy`].
    pub enable_stabilize: bool,
    /// Tick budget for the first stable/focused switch; each subsequent
    /// switch's budget grows quadratically in the number of switches so far.
    pub stabilize_base: u64,
    /// Luby restart cap used specifically during *focused* mode (`0` =
    /// uncapped). Stable mode's restarts are driven by the reluctant-doubling
    /// clock instead and are not capped here.
    pub focused_luby_cap: u64,
    /// Restart count between rephase rounds (periodic saved-polarity flips
    /// meant to let a restart explore a genuinely different region instead of
    /// re-deriving the trail it just abandoned). `0` disables rephasing.
    /// Rephasing only fires while the search is in stable mode — see
    /// `Solver::restart`'s internals for why (a private method, not part of
    /// this crate's public API).
    pub rephase_interval: u32,
    /// Reuse-trail restarts (Heule/Möhle & Biere): instead of always
    /// backtracking to the root, keep the longest decision prefix whose
    /// variables are still at least as "important" (by VSIDS activity) as the
    /// next variable the search would decide anyway — that prefix would
    /// simply be re-derived, so throwing it away is pure waste.
    pub reuse_trail: bool,
    /// Optional external branching heuristic. When `Some`, called before built-in
    /// VSIDS/LRB/CHB; returning `None` from the heuristic falls back to built-in.
    /// Default: `None` (pure built-in strategy).
    pub external_branching: Option<BoxedBranchingHeuristic>,
    /// Run failed-literal probing (with on-the-fly hyper-binary resolution)
    /// once before search starts. For each still-unassigned variable, both
    /// polarities are tentatively propagated at decision level 0; a polarity
    /// that conflicts is a *failed literal* and its negation is forced as a
    /// permanent unit. Bounded by an internal propagation budget, so it never
    /// dominates on any instance size, and unlike bounded variable
    /// elimination / equivalent-literal substitution it never removes a
    /// variable (only forces facts), so it carries none of their
    /// incremental-scope caveat. Off by default anyway: on some instances a
    /// probing-only pass is enough to settle the verdict without the main
    /// CDCL loop ever running, which is sound but changes observable solve
    /// behavior (e.g. how many times conflict-analysis hooks fire) — opt-in
    /// until a caller has confirmed that shape is acceptable for their use.
    pub enable_failed_literal_probing: bool,
    /// Bounded variable elimination (SatELite-style): resolve away a variable
    /// whose defining clauses are cheap to fold together, replacing them with
    /// their resolvents. Off by default — unlike probing this *removes*
    /// variables from the live formula, which is unsound across an
    /// incremental scope (a later `push`/`add_clause` could reintroduce the
    /// eliminated polarity) and is therefore only ever run at the base
    /// assertion level. Mutually exclusive with
    /// [`SolverConfig::enable_equiv_substitution`] in this implementation —
    /// see `Solver::bounded_variable_elimination`'s internals (a private
    /// method, not part of this crate's public API) for why combining the
    /// two reconstruction maps in one pass is not yet supported.
    ///
    /// Known limitation shared with `enable_equiv_substitution`: neither is
    /// consulted by [`Solver::solve_with_assumptions`], which assigns
    /// assumption literals without checking whether the toolkit already
    /// eliminated that variable. Assuming a literal on a variable this pass
    /// (or substitution) removed leaves it unconstrained by any live clause,
    /// so the assumption trivially "succeeds" and `save_model`'s
    /// unconditional reconstruction then overwrites it — a model that can
    /// violate the caller's own assumption. Narrow (opt-in BVE/substitution
    /// *and* assumption-based solving on the same solver instance) and not
    /// addressed in this pass; do not combine them.
    pub enable_bve: bool,
    /// Equivalent-literal substitution: find literals proven equivalent by a
    /// cycle in the binary implication graph (Tarjan SCC) and rewrite every
    /// clause through a single representative per class. Off by default for
    /// the same incremental-scope reason as [`SolverConfig::enable_bve`], and
    /// mutually exclusive with it (see there) — including the same
    /// `solve_with_assumptions` limitation documented on that field.
    pub enable_equiv_substitution: bool,
    /// When [`SolverConfig::enable_equiv_substitution`] is set, also run
    /// AND/XOR gate congruence detection first and fold the detected
    /// equivalences into the binary implication graph before the SCC pass —
    /// this is what lets equivalent-literal substitution collapse structural
    /// duplication (e.g. repeated partial-product/full-adder gates in a
    /// multiplier) that plain binary clauses do not expose. Ignored when
    /// `enable_equiv_substitution` is off.
    pub enable_gate_congruence: bool,
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
            .field("use_vmtf", &self.use_vmtf)
            .field("luby_cap", &self.luby_cap)
            .field("enable_stabilize", &self.enable_stabilize)
            .field("stabilize_base", &self.stabilize_base)
            .field("focused_luby_cap", &self.focused_luby_cap)
            .field("rephase_interval", &self.rephase_interval)
            .field("reuse_trail", &self.reuse_trail)
            .field(
                "external_branching",
                &self
                    .external_branching
                    .as_ref()
                    .map(|_| "<BranchingHeuristic>"),
            )
            .field(
                "enable_failed_literal_probing",
                &self.enable_failed_literal_probing,
            )
            .field("enable_bve", &self.enable_bve)
            .field("enable_equiv_substitution", &self.enable_equiv_substitution)
            .field("enable_gate_congruence", &self.enable_gate_congruence)
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

impl Default for SolverConfig {
    fn default() -> Self {
        Self {
            restart_interval: 100,
            restart_multiplier: 1.5,
            clause_deletion_threshold: 10000,
            var_decay: 0.95,
            clause_decay: 0.999,
            random_polarity_prob: 0.02,
            restart_strategy: RestartStrategy::Luby,
            enable_lazy_hyper_binary: true,
            use_chb_branching: false,
            use_lrb_branching: false,
            enable_inprocessing: false,
            inprocessing_interval: 5000,
            enable_chronological_backtrack: true,
            chrono_backtrack_threshold: 100,
            use_vmtf: true,
            luby_cap: 64,
            enable_stabilize: true,
            stabilize_base: 5000,
            focused_luby_cap: 16,
            // Rephasing only pays off once other benchmarking has tuned an
            // interval for a given workload; off by default so a freshly
            // created solver behaves exactly like `enable_stabilize` alone
            // predicts. Presets opt into a tuned interval explicitly.
            rephase_interval: 0,
            reuse_trail: true,
            external_branching: None,
            // Off by default: although sound (it only ever forces facts, never
            // removes a variable), a probing-only pass can fully settle a
            // small/dense instance's verdict before the main CDCL loop ever
            // runs, changing observable solve behavior (conflict-analysis
            // hooks firing zero times on an UNSAT instance, for one) even
            // though the reported verdict itself never changes. Opt-in until
            // a caller has confirmed that shape.
            enable_failed_literal_probing: false,
            // BVE and equivalent-literal substitution both delete variables
            // from the live formula (recording reconstruction data to fix
            // their model value back up afterward), which is only sound at
            // the base assertion level with no active incremental `push` in
            // scope. Left opt-in until a caller has confirmed that shape.
            enable_bve: false,
            enable_equiv_substitution: false,
            enable_gate_congruence: false,
        }
    }
}
