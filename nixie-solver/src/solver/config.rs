//! Solver settings: the logic, the search configuration and the individual
//! switches, plus the polarity analysis and datatype constructor extraction
//! that hang off them.
//!
//! These methods are extracted from `mod.rs` to keep that file under the
//! 2000-line refactoring threshold.
//!
//! # Every mutator here goes through [`Solver::settings_changed`]
//!
//! A [`Solver::check`] reads two things: the assertion stack, and the settings
//! in this module.  The assertion stack has its own invalidation hook
//! (`Solver::invalidate_results`, called from `assert` / `push` / `pop` /
//! `reset`); this module is the other half.  A setter that changed a lever the
//! solve loop honours *without* announcing it would let the cached verdict of
//! [`crate::solver::verdict_cache`] answer a question it was never asked –
//! `(check-sat)` timing out, `:timeout` being raised, and the same `unknown`
//! coming straight back out of the cache.  So the rule is mechanical: **every
//! `&mut self` method in this module ends by calling
//! [`Solver::settings_changed`]**, and the fingerprint additionally carries the
//! settings by value so a future setter that forgets is still caught.

use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_theories::arithmetic::ArithSolver;

use super::Solver;
use super::types::{Polarity, SolverConfig};

impl Solver {
    /// Announce that a solver *setting* has changed.
    ///
    /// Bumps [`Solver::settings_epoch`] (which the goal fingerprint carries) and
    /// drops the cached verdict, so the next [`Solver::check`] runs a real
    /// search under the new settings instead of replaying one run under the old
    /// ones.
    ///
    /// # Why this drops the verdict but not the model
    ///
    /// A model and an unsat core are statements about the *assertion stack*, and
    /// a setting change does not move it: a model that satisfied every assertion
    /// still satisfies them under a different timeout or random seed, so
    /// `(get-model)` stays answerable.  A cached verdict is different – it is a
    /// statement about what *this configuration's search* concluded, and
    /// `Unknown` in particular is a statement about resource exhaustion rather
    /// than about the goal.  Handing back an `Unknown` produced under a
    /// millisecond budget to a caller who has just raised the budget to ten
    /// minutes is simply a wrong answer to the question asked, and the same
    /// applies to answering with a verdict computed while unsat-core production
    /// was off (there is no core to hand over afterwards) or before a new random
    /// seed was supposed to perturb which model comes back.
    pub(super) fn settings_changed(&mut self) {
        self.settings_epoch = self.settings_epoch.wrapping_add(1);
        self.certification_failure = None;
        self.last_check = None;
    }

    /// Get the configuration
    #[must_use]
    pub fn config(&self) -> &SolverConfig {
        &self.config
    }

    /// Replace the whole search configuration.
    pub fn set_config(&mut self, config: SolverConfig) {
        self.config = config;
        self.settings_changed();
        // Push the SAT search-schedule fields into the already-built engine
        // (they are consumed live there). Other SAT-side fields remain
        // construction-only - see `with_config`.
        let (rs, inp, int) = (
            self.config.restart_strategy,
            self.config.enable_inprocessing,
            self.config.inprocessing_interval,
        );
        self.sat.update_search_config(rs, inp, int);
    }

    /// Why certified mode declined the most recent candidate verdict.
    #[must_use]
    pub fn certification_failure(&self) -> Option<&str> {
        self.certification_failure.as_deref()
    }

    /// Set a wall-clock timeout.
    pub fn set_timeout(&mut self, timeout: core::time::Duration) {
        self.config.timeout_ms = u64::try_from(timeout.as_millis()).unwrap_or(u64::MAX);
        self.settings_changed();
    }

    /// Set the maximum number of SAT conflicts.
    pub fn set_conflict_limit(&mut self, max_conflicts: u64) {
        self.config.max_conflicts = max_conflicts;
        self.settings_changed();
    }

    /// Set the maximum number of SAT decisions.
    pub fn set_decision_limit(&mut self, max_decisions: u64) {
        self.config.max_decisions = max_decisions;
        self.settings_changed();
    }

    /// Enable or disable theory-aware branching
    pub fn set_theory_aware_branching(&mut self, enabled: bool) {
        self.theory_aware_branching = enabled;
        self.settings_changed();
    }

    /// Enable or disable unsat core production
    pub fn set_produce_unsat_cores(&mut self, produce: bool) {
        self.produce_unsat_cores = produce;
        self.settings_changed();
    }

    /// Seed the embedded SAT engine's phase-randomization PRNG.
    ///
    /// This realises the SMT-LIB `:random-seed` option: the SAT solver samples a
    /// random phase with probability `random_polarity_prob` (nonzero by default),
    /// so the seed genuinely perturbs the decision order and hence which model is
    /// returned for a satisfiable problem – while never affecting the sat/unsat
    /// verdict (soundness is seed-independent).  A seed of `0` reproduces the
    /// default out-of-the-box behaviour.
    pub fn set_random_seed(&mut self, seed: u64) {
        self.sat.set_random_seed(seed);
        self.settings_changed();
    }

    /// Set the logic
    ///
    /// Engine routing derives from the **registry spec** (`logic_contract`),
    /// never from name substrings.  Known-header semantics per the SMT-LIB
    /// catalog entry; `ALL`/unknown names keep the constructor defaults and
    /// route structurally at check time (`check_nlsat`'s open-logic shape
    /// detection) — matching the historical `ALL` behavior exactly, so
    /// trajectory parity holds for headerless inputs.
    ///
    /// Substring bugs this replaces: `QF_NIRA` contains neither "LIA" nor
    /// "LRA", so its linear-fallback arithmetic solver stayed the default
    /// LRA even though NIRA includes integer terms; the registry's
    /// `arith ∧ integer` field routes it (and AUFNIRA) to LIA.
    pub fn set_logic(&mut self, logic: &str) {
        self.logic = Some(logic.to_string());
        self.settings_changed();

        // `Err` (unknown name) reaches here only via direct
        // `Solver::set_logic` calls — the Context layer rejects unknown
        // names at the script surface.  Route as `ALL` (defaults + shape
        // detection) rather than partially reconfiguring.
        let spec = crate::solver::logic_contract::lookup(logic).ok().flatten();
        let Some(spec) = spec else {
            return;
        };
        if spec.arith && spec.nonlinear {
            // Nonlinear: NLSAT primary; the linear fallback keeps every
            // linear atom answerable.  Per-sort integrality in the
            // translator handles mixed NIRA.
            #[cfg(feature = "nlsat")]
            {
                self.nlsat = Some(nixie_theories::nlsat::NlsatTheory::new(spec.integer));
            }
            self.arith = if spec.integer {
                ArithSolver::lia()
            } else {
                ArithSolver::lra()
            };
            #[cfg(feature = "tracing")]
            tracing::info!(
                "NLSAT solver engaged for {logic} (nonlinear, integer={})",
                spec.integer
            );
        } else if spec.arith {
            self.arith = if spec.integer {
                ArithSolver::lia()
            } else {
                ArithSolver::lra()
            };
        } else if spec.bv {
            // BV comparisons are handled as bounded integer arithmetic.
            self.arith = ArithSolver::lia();
        }
        // QF_UF and other theory-only logics: keep the default.

        // NOTE: the VSIDS + arith-bound-prop configuration that previously
        // gated on `matches!(logic, "QF_UFIDL")` is applied from the
        // *features* of the asserted formula in [`Self::apply_feature_routing`]
        // (`is_diff_logic() && has_uf()`), the `CFG_AUTO` analogue of Z3's
        // `setup_QF_UFIDL(static_features&)` — it cannot run here because
        // the assertions are not available at `set-logic` time.
    }

    /// Feature-driven search-knob routing – the `CFG_AUTO` half of Z3's
    /// `smt_setup.cpp`.
    ///
    /// Called once per [`Solver::check_core`] after [`StaticFeatures`] are
    /// collected.  Each decision here mirrors a knob a Z3
    /// `setup_QF_X(static_features & st)` routine sets from the formula rather
    /// than the file name; the declared logic remains the coarse router (it
    /// picked the arithmetic solver in [`Self::set_logic`]).
    ///
    /// `ufidl_shape` is `is_diff_logic(st) && has_uf(st) && logic-allows-DL` –
    /// the shape `setup_QF_UFIDL(st)` fires on.
    ///
    /// # Soundness
    ///
    /// Every switch flipped here is a search heuristic (branching order); none
    /// of them changes the sat/unsat verdict, so feature-misclassification only
    /// ever costs performance, never correctness.
    pub(super) fn apply_feature_routing(&mut self, ufidl_shape: bool) {
        self.route_branching_from_features(ufidl_shape);
    }

    /// VSIDS branching for the difference-logic + UF shape (Z3's
    /// `setup_QF_UFIDL(st)`), gated on the formula features instead of the
    /// logic name.  VSIDS + incremental arith-bound-propagation is the lever
    /// that closes the finite-domain UFIDL `vhard` family; Z3 reaches the same
    /// configuration from `is_diff_logic(st)` + UF counts rather than from
    /// `m_logic == "QF_UFIDL"`.
    ///
    /// Gating on features fixes the two failure modes of the old logic-string
    /// gate: a benchmark that *declares* `QF_UFIDL` but is not actually
    /// difference logic no longer gets the unsound derived-reason path, and one
    /// that declares no logic but is UFIDL-shaped still does.
    #[cfg(feature = "std")]
    fn route_branching_from_features(&mut self, ufidl_shape: bool) {
        use crate::solver::theory_manager::{BoundPropMode, arith_bound_prop_mode};
        if arith_bound_prop_mode() != BoundPropMode::Off && ufidl_shape {
            self.sat.set_branching_vsids();
        }
    }

    #[cfg(not(feature = "std"))]
    fn route_branching_from_features(&mut self, _ufidl_shape: bool) {}

    /// Extract (variable, constructor) pair from an equality if one side is a variable
    /// and the other is a DtConstructor
    pub(super) fn extract_dt_var_constructor(
        &self,
        lhs: TermId,
        rhs: TermId,
        manager: &TermManager,
    ) -> Option<(TermId, nixie_core::interner::Spur)> {
        let lhs_term = manager.get(lhs)?;
        let rhs_term = manager.get(rhs)?;

        // lhs is var, rhs is constructor
        if matches!(lhs_term.kind, TermKind::Var(_)) {
            if let TermKind::DtConstructor { constructor, .. } = &rhs_term.kind {
                return Some((lhs, *constructor));
            }
        }
        // rhs is var, lhs is constructor
        if matches!(rhs_term.kind, TermKind::Var(_)) {
            if let TermKind::DtConstructor { constructor, .. } = &lhs_term.kind {
                return Some((rhs, *constructor));
            }
        }
        None
    }

    /// Collect polarity information for all subterms
    /// This is used for polarity-aware encoding optimization
    ///
    /// Iterative: `(term, polarity)` work items on an explicit heap stack, so
    /// nesting depth cannot overflow the native call stack.  The stored
    /// polarity of every term is a monotone join (towards `Both`), so a visit
    /// that does not change a term's stored polarity re-delivers exactly what
    /// an earlier visit already propagated to its subterms and is pruned;
    /// this both preserves the final `polarities` map exactly and bounds the
    /// work to three productive visits per term on a shared DAG.
    pub(super) fn collect_polarities(
        &mut self,
        term: TermId,
        polarity: Polarity,
        manager: &TermManager,
    ) {
        let mut stack: Vec<(TermId, Polarity)> = vec![(term, polarity)];
        while let Some((term, polarity)) = stack.pop() {
            // Update the polarity for this term
            let current = self.polarities.get(&term).copied();
            let new_polarity = match (current, polarity) {
                (Some(Polarity::Both), _) | (_, Polarity::Both) => Polarity::Both,
                (Some(Polarity::Positive), Polarity::Negative)
                | (Some(Polarity::Negative), Polarity::Positive) => Polarity::Both,
                (Some(p), _) => p,
                (None, p) => p,
            };

            // A visit that leaves the stored polarity unchanged would deliver
            // the very propagation an earlier visit with the same join result
            // already delivered, so its subterm walk is redundant.  (This
            // subsumes the previous `current == Some(Both)` early-out.)
            if current == Some(new_polarity) {
                continue;
            }
            self.polarities.insert(term, new_polarity);

            let Some(t) = manager.get(term) else {
                continue;
            };

            // Children are pushed in reverse so they pop in the original
            // left-to-right order.
            match &t.kind {
                TermKind::Not(arg) => {
                    let neg_polarity = match polarity {
                        Polarity::Positive => Polarity::Negative,
                        Polarity::Negative => Polarity::Positive,
                        Polarity::Both => Polarity::Both,
                    };
                    stack.push((*arg, neg_polarity));
                }
                TermKind::And(args) | TermKind::Or(args) => {
                    stack.extend(args.iter().rev().map(|&arg| (arg, polarity)));
                }
                TermKind::Implies(lhs, rhs) => {
                    let neg_polarity = match polarity {
                        Polarity::Positive => Polarity::Negative,
                        Polarity::Negative => Polarity::Positive,
                        Polarity::Both => Polarity::Both,
                    };
                    stack.push((*rhs, polarity));
                    stack.push((*lhs, neg_polarity));
                }
                TermKind::Ite(cond, then_br, else_br) => {
                    stack.push((*else_br, polarity));
                    stack.push((*then_br, polarity));
                    stack.push((*cond, Polarity::Both));
                }
                TermKind::Xor(lhs, rhs) | TermKind::Eq(lhs, rhs) => {
                    // For XOR and Eq, both sides appear in both polarities
                    stack.push((*rhs, Polarity::Both));
                    stack.push((*lhs, Polarity::Both));
                }
                TermKind::Let { bindings, body } => {
                    // The parser inlines let-bound values into the body, so the
                    // body carries the real structure and inherits this
                    // occurrence's polarity.  Binding values are visited with
                    // `Both` because an unused binding is still part of the term
                    // DAG.  (Ported from main's hyper-binary-resolution
                    // soundness fix: upstream's refactor to an iterative walk
                    // dropped this descent, so everything under the parser's
                    // wrapping `Let` contributed no polarity, under-constraining
                    // shared Plaisted-Greenbaum gates.)
                    stack.push((*body, polarity));
                    for (_name, value) in bindings.iter().rev() {
                        stack.push((*value, Polarity::Both));
                    }
                }
                other => {
                    // Soundness: any *Boolean* sub-formula we do not descend
                    // into structurally must still be marked `Both`.  `encode`
                    // reads this map to decide whether a shared And/Or gate may
                    // be given a one-sided (Plaisted-Greenbaum) encoding, and
                    // gates are hash-consed across assertions.  Silently skipping
                    // an occurrence therefore does not mean "no information" – it
                    // means the gate keeps whatever one-sided polarity some other
                    // assertion recorded, so the implication direction this
                    // occurrence needed may never be emitted and the gate is
                    // under-constrained.  Marking `Both` only costs the PG
                    // optimisation, never soundness.
                    let mut children = Vec::new();
                    super::term_walk::collect_structural_children(other, &mut children);
                    let bool_sort = manager.sorts.bool_sort;
                    for child in children.iter().rev() {
                        if manager.get(*child).is_some_and(|t| t.sort == bool_sort) {
                            stack.push((*child, Polarity::Both));
                        }
                    }
                }
            }
        }
    }
}
