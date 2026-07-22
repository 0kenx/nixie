//! MBQI Integration with Main Solver
//!
//! This module handles the integration of MBQI with the main SMT solver.
//! It provides callbacks, communication interfaces, and coordination logic.

#![allow(missing_docs)]

#[allow(unused_imports)]
use crate::prelude::*;
use core::fmt;
use oxiz_core::ast::traversal::collect_free_vars;
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::interner::Spur;
use oxiz_core::sort::{SortId, SortKind};
use smallvec::SmallVec;
#[cfg(feature = "std")]
use std::time::{Duration, Instant};

use super::conflict_driven::ConflictScores;
use super::counterexample::CounterExampleGenerator;
use super::finite_model::FiniteModelFinder;
use super::heuristics::MBQIBudget;
use super::instantiation::InstantiationEngine;
use super::lazy_instantiation::LazyInstantiator;
use super::model_completion::CompletedModel;
use super::model_completion::ModelCompleter;
use super::sat_certify;
use super::{Instantiation, MBQIResult, MBQIStats, QuantifiedFormula, QuantifierId};

/// Upper bound on the number of candidate values the counterexample generator
/// enumerates per bound variable.
///
/// This MUST stay in sync with
/// [`CounterExampleGenerator::max_candidates_per_var`](super::counterexample).
/// It is used to decide whether a *finite* domain (e.g. a small uninterpreted
/// sort universe) was enumerated *exhaustively*: only then can the absence of a
/// counterexample be reported as a genuine `Satisfied` (sat) result. A finite
/// sample over an infinite or incompletely-enumerated domain proves nothing.
const FINITE_ENUM_LIMIT: usize = 10;

/// Upper bound on the number of candidate *tuples* (cartesian-product
/// combinations across all bound variables) the counterexample generator
/// enumerates for a single quantifier.
///
/// This MUST stay in sync with the `max_cex_per_quantifier * 20` bound passed
/// to [`CounterExampleGenerator::enumerate_combinations`](super::counterexample)
/// from `generate` (currently `5 * 20 = 100`).
///
/// Enumeration is truncated once this many combinations have been produced, and
/// the generator does **not** lower `all_evaluations_ground` on that truncation
/// (the odometer varies variable 0 fastest, so trailing variables never leave
/// their first candidate).  Therefore, even when every individual bound variable
/// ranges over a genuinely finite domain, the absence of a counterexample proves
/// satisfaction **only** when the *product* of the per-variable candidate-domain
/// sizes does not exceed this cap -- otherwise some tuples were never tried and
/// `Satisfied` (sat) would be unsound.
const COMBINATION_ENUM_CAP: usize = 100;

/// Upper bound on the number of instantiation tuples the SAT-certification pass
/// ([`super::sat_certify`]) enumerates per quantifier.
///
/// Certification enumerates the *complete* relevant / bounded domain (never a
/// truncated sample), so this cap bounds work without affecting soundness: a
/// quantifier whose relevant domain exceeds the cap is simply reported
/// ineligible and handled by the normal path.  It comfortably covers the target
/// benchmarks (e.g. two Int variables bounded to `[0, 10]` give 121 tuples).
const SAT_CERTIFY_CAP: usize = 4096;

/// Callback trait for solver communication
pub trait SolverCallback: fmt::Debug {
    /// Called when new instantiations are generated
    fn on_instantiation(&mut self, inst: &Instantiation);

    /// Called when a conflict is detected
    fn on_conflict(&mut self, quantifier: TermId, reason: &[TermId]);

    /// Called when MBQI starts a new round
    fn on_round_start(&mut self, round: usize);

    /// Called when MBQI completes a round
    fn on_round_end(&mut self, round: usize, result: &MBQIResult);

    /// Check if solver should stop (e.g., timeout)
    fn should_stop(&self) -> bool;
}

/// MBQI integration manager
#[derive(Debug)]
pub struct MBQIIntegration {
    /// Model completer
    model_completer: ModelCompleter,
    /// Instantiation engine
    instantiation_engine: InstantiationEngine,
    /// Lazy instantiator
    lazy_instantiator: LazyInstantiator,
    /// Finite model finder
    finite_model_finder: FiniteModelFinder,
    /// Counterexample generator
    cex_generator: CounterExampleGenerator,
    /// Tracked quantifiers
    quantifiers: Vec<QuantifiedFormula>,
    /// Generated instantiations (for deduplication)
    generated_instantiations: FxHashMap<InstantiationKey, usize>,
    /// Extra candidate terms per sort (e.g. Skolem function applications)
    extra_candidates: FxHashMap<SortId, Vec<TermId>>,
    /// Whether blind instantiation has been attempted (one-shot guard)
    blind_attempted: bool,
    /// Current round number
    current_round: usize,
    /// Per-round instantiation budget.
    budget: MBQIBudget,
    /// Conflict-driven quantifier activity.
    conflict_scores: ConflictScores,
    /// Maximum rounds
    max_rounds: usize,
    /// Time limit
    #[cfg(feature = "std")]
    time_limit: Option<Duration>,
    /// Start time
    #[cfg(feature = "std")]
    start_time: Option<Instant>,
    /// Statistics
    stats: MBQIStats,
}

impl MBQIIntegration {
    /// Create a new MBQI integration
    pub fn new() -> Self {
        Self {
            model_completer: ModelCompleter::new(),
            instantiation_engine: InstantiationEngine::new(),
            lazy_instantiator: LazyInstantiator::new(),
            finite_model_finder: FiniteModelFinder::new(),
            cex_generator: CounterExampleGenerator::new(),
            quantifiers: Vec::new(),
            generated_instantiations: FxHashMap::default(),
            extra_candidates: FxHashMap::default(),
            blind_attempted: false,
            current_round: 0,
            budget: MBQIBudget::new(1024),
            conflict_scores: ConflictScores::new(0.95),
            max_rounds: 100,
            #[cfg(feature = "std")]
            time_limit: Some(Duration::from_secs(60)),
            #[cfg(feature = "std")]
            start_time: None,
            stats: MBQIStats::new(),
        }
    }

    /// Add a quantified formula
    pub fn add_quantifier(&mut self, term: TermId, manager: &TermManager) {
        let Some(t) = manager.get(term) else {
            return;
        };

        match &t.kind {
            oxiz_core::ast::TermKind::Forall { vars, body, .. } => {
                let bound_vars: SmallVec<[(Spur, SortId); 4]> = vars.iter().copied().collect();
                self.quantifiers
                    .push(QuantifiedFormula::new(term, bound_vars, *body, true));
                self.stats.num_quantifiers += 1;
            }
            oxiz_core::ast::TermKind::Exists { vars, body, .. } => {
                let bound_vars: SmallVec<[(Spur, SortId); 4]> = vars.iter().copied().collect();
                self.quantifiers
                    .push(QuantifiedFormula::new(term, bound_vars, *body, false));
                self.stats.num_quantifiers += 1;
            }
            _ => {}
        }
    }

    /// Run MBQI with a partial model implementing the Ge & de Moura (2009) algorithm.
    ///
    /// The loop:
    /// 1. Complete the partial model (fill in defaults, function interps, universes)
    /// 2. For each tracked quantifier, check against the completed model
    /// 3. If counterexamples found, generate instantiation lemmas and return them
    /// 4. If no counterexamples for any quantifier, the model satisfies all -- return SAT
    pub fn run(
        &mut self,
        partial_model: &FxHashMap<TermId, TermId>,
        manager: &mut TermManager,
        callback: &mut dyn SolverCallback,
    ) -> MBQIResult {
        #[cfg(feature = "std")]
        {
            self.start_time = Some(Instant::now());
        }

        if self.quantifiers.is_empty() {
            return MBQIResult::NoQuantifiers;
        }

        // Clear the candidate cache at the start of each MBQI round so that
        // new ground terms (e.g. Skolem applications like sk(0)) created by
        // previous instantiation rounds are discovered as fresh candidates.
        self.cex_generator.clear_cache();

        // Check round limit. `current_round` is deliberately NOT reset here:
        // `run()` is invoked once per outer solver iteration (see
        // `check_with_model`), so the counter must accumulate across calls
        // for `max_rounds` to bound the *total* number of MBQI rounds for a
        // single `solve()` invocation. It is reset only by `clear()` (a new
        // solve) or `MBQIIntegration::new()`.
        if self.current_round >= self.max_rounds {
            self.update_final_stats();
            return MBQIResult::Unknown;
        }

        if self.check_timeout() || callback.should_stop() {
            return MBQIResult::Unknown;
        }

        self.current_round += 1;
        if self.current_round > 1 {
            self.conflict_scores.decay_on_restart();
        }
        let quantifier_ids: Vec<QuantifierId> = self.quantifiers.iter().map(|q| q.term).collect();
        self.budget
            .carve_per_quantifier(&quantifier_ids, Some(&self.conflict_scores));
        callback.on_round_start(self.current_round);
        self.stats.num_checks += 1;

        #[cfg(feature = "std")]
        let round_start = Instant::now();

        // Step 1: Complete the model with proper Ge & de Moura completion
        let completed_model =
            match self
                .model_completer
                .complete(partial_model, &self.quantifiers, manager)
            {
                Ok(model) => {
                    self.stats.num_completions += 1;
                    model
                }
                Err(_) => {
                    callback.on_round_end(self.current_round, &MBQIResult::Unknown);
                    return MBQIResult::Unknown;
                }
            };

        #[cfg(feature = "std")]
        {
            self.stats.completion_time_us += round_start.elapsed().as_micros() as u64;
        }

        // Step 2: Check each quantifier against the completed model
        //         and generate counterexample-based instantiations
        #[cfg(feature = "std")]
        let cex_start = Instant::now();
        let mut all_instantiations = Vec::new();
        // Track whether ALL quantifier evaluations resolved to concrete
        // boolean values.  We can only claim Satisfied when every evaluation
        // across every quantifier was fully ground (i.e. concrete True).
        let mut all_evaluations_fully_ground = true;

        // Collect quantifiers first to avoid borrow checker issues
        let quantifiers: Vec<_> = self.quantifiers.to_vec();

        // Fast path: if every instantiable quantifier has a body that
        // simplifies to `true` independently of its bound variables (e.g.
        // `forall x. f(x) = f(x)`), the whole quantified block is valid over
        // its entire domain — infinite or not — so the model already satisfies
        // it.  Recognizing this up front (before any enumerative
        // instantiation) restores `Satisfied` (sat) in a single round for
        // simple UFLIA-style tautological quantifiers that the finite-domain
        // sampler alone cannot certify because the bound variable ranges over
        // the infinite Int domain.
        if self.all_quantifiers_trivially_valid(&quantifiers, manager) {
            let result = MBQIResult::Satisfied;
            callback.on_round_end(self.current_round, &result);
            self.update_final_stats();
            return result;
        }

        // Sound SAT certification for the (almost-)uninterpreted / bounded
        // fragment via complete instantiation (Ge & de Moura 2009).
        //
        // The certifier returns the *complete* set of relevant/bounded
        // instantiation lemmas for every eligible quantifier.  We deduplicate
        // against instances emitted in earlier rounds:
        //
        //   * some lemma is fresh  -> add it and re-solve (refine);
        //   * every lemma is a duplicate (the set is *saturated*) -> the ground
        //     solver already produced a model of every relevant instance, so by
        //     the completeness theorem the whole quantified formula is `Sat`.
        //
        // The `Sat` conclusion rests on the ground solver's own model over the
        // real assertions, never on the (possibly incomplete) completed model:
        // a universal instance is always a sound consequence, so this can turn
        // an unsatisfiable goal into a detected conflict but never fabricate
        // `Sat`.  Goals outside the fragment yield `NotEligible` and fall
        // through to the normal counterexample path (and ultimately `Unknown`).
        match sat_certify::collect_fragment_instances(
            &quantifiers,
            &completed_model,
            manager,
            SAT_CERTIFY_CAP,
            self.current_round as u32,
        ) {
            sat_certify::CertifyResult::Instances(insts) => {
                let mut fresh = Vec::new();
                for mut inst in insts {
                    if self.is_duplicate(&inst) {
                        continue;
                    }
                    // Record against the (quantifier, binding) key *before* the
                    // tautology filter below.  Saturation is detected purely by
                    // this key (never by the result term), so recording every
                    // relevant tuple — even those whose body collapses to `true`
                    // — is what lets a later round observe "nothing fresh" and
                    // conclude `Satisfied` soundly.
                    self.record_instantiation(&inst);

                    // Simplify so that the concrete guards of a bounded-box
                    // instance collapse: e.g.
                    //   (and (>= 1 0) (<= 1 10) (= (f 1) (f 2))) => (= 1 2)
                    // reduces to the clean disequality (not (= (f 1) (f 2))).
                    // Emitting the raw guarded implication instead feeds the
                    // downstream pigeonhole / integer-domain clause heuristics a
                    // spurious "bounded integer variable" shape (the substituted
                    // constants still parse as `(>= c 0) (<= c 10)` conjuncts),
                    // which over-constrains the ground problem and can flip a
                    // satisfiable goal to a spurious `unsat`.  This mirrors the
                    // enumerative path, which simplifies for the same reason.
                    inst.result = self.deep_simplify(inst.result, manager);

                    // A tautology instance (body ≡ ⊤) constrains nothing.  It is
                    // already recorded above (so the set can still saturate), so
                    // just skip emitting it as a lemma.
                    if manager
                        .get(inst.result)
                        .is_some_and(|t| matches!(t.kind, TermKind::True))
                    {
                        continue;
                    }

                    callback.on_instantiation(&inst);
                    fresh.push(inst);
                }
                let result = if fresh.is_empty() {
                    // Saturated: every relevant instance was either emitted in an
                    // earlier round or is a tautology, and the ground solver still
                    // found a model — so by the completeness theorem for this
                    // fragment the whole quantified formula is `Sat`.
                    MBQIResult::Satisfied
                } else {
                    MBQIResult::NewInstantiations(fresh)
                };
                callback.on_round_end(self.current_round, &result);
                self.update_final_stats();
                return result;
            }
            sat_certify::CertifyResult::NotEligible => {
                // Not in the certifiable fragment: keep the normal behaviour.
            }
        }

        for quantifier in &quantifiers {
            if !quantifier.can_instantiate() {
                continue;
            }

            // Inject extra candidates (e.g. Skolem terms) into the
            // counterexample generator before searching.
            self.cex_generator
                .inject_extra_candidates(&self.extra_candidates);

            // Use the counterexample generator directly to find
            // assignments that falsify the quantifier body
            let cex_result = self
                .cex_generator
                .generate(quantifier, &completed_model, manager);

            if !cex_result.all_evaluations_ground {
                all_evaluations_fully_ground = false;
            }

            self.stats.num_counterexamples += cex_result.counterexamples.len();

            for cex in &cex_result.counterexamples {
                if !self.budget.consume(quantifier.term, 1) {
                    break;
                }
                // Build the instantiation lemma: body[x1/v1, ..., xn/vn].
                // A `None` result means the substituted body still contained a
                // bound variable of this quantifier as a free occurrence -- an
                // internal error; such a lemma must never be emitted.
                let Some(ground_body) =
                    self.apply_substitution(quantifier, &cex.assignment, manager)
                else {
                    continue;
                };

                let inst = cex.to_instantiation(ground_body);

                if !self.is_duplicate(&inst) {
                    self.record_instantiation(&inst);
                    callback.on_instantiation(&inst);
                    all_instantiations.push(inst);
                }
            }

            // Also try instantiation engine strategies (pattern-based, enumerative),
            // but ONLY for universal quantifiers.
            //
            // For existential quantifiers: the engine generates body[i/v] lemmas saying
            // "body must be true here" without verifying that body IS true for that
            // candidate. Adding False instantiation lemmas for existentials directly
            // contradicts the asserted constraints and produces spurious UNSAT.
            // If no witness was found by the counterexample generator, return Unknown.
            if cex_result.counterexamples.is_empty() && quantifier.is_universal {
                let engine_insts =
                    self.instantiation_engine
                        .instantiate(quantifier, &completed_model, manager);

                for inst in engine_insts {
                    if !self.budget.consume(quantifier.term, 1) {
                        break;
                    }
                    if !self.is_duplicate(&inst) {
                        self.record_instantiation(&inst);
                        callback.on_instantiation(&inst);
                        all_instantiations.push(inst);
                    }
                }
            } else if cex_result.counterexamples.is_empty() && !quantifier.is_universal {
                // For existentials with no witness found, mark as not-all-ground so
                // we return Unknown rather than Satisfied (we couldn't verify).
                all_evaluations_fully_ground = false;
            }
        }

        #[cfg(feature = "std")]
        {
            self.stats.cex_search_time_us += cex_start.elapsed().as_micros() as u64;
        }

        // Step 3: Check result
        if all_instantiations.is_empty() {
            if all_evaluations_fully_ground
                && self.all_domains_finitely_exhausted(&quantifiers, &completed_model, manager)
            {
                // Every quantifier body evaluated to concrete True under every
                // candidate assignment AND every bound variable ranged over a
                // genuinely finite domain that was enumerated *exhaustively*
                // (e.g. Bool, or a small uninterpreted-sort universe).  Only
                // then does the completed model provably satisfy all
                // quantifiers, so `Satisfied` (sat) is sound.
                let result = MBQIResult::Satisfied;
                callback.on_round_end(self.current_round, &result);
                self.update_final_stats();
                return result;
            }
            // Otherwise: either some evaluations produced symbolic residuals,
            // OR a bound variable ranged over an infinite domain (Int, Real,
            // String, ...) or a domain that was only *sampled* rather than
            // fully enumerated (BitVec, large universes, ...).  A finite sample
            // over such a domain proves nothing -- for example every candidate
            // in `-2..=5` satisfies `(>= x (- 10))` even though the universal
            // is false at `x = -11`.  We must NOT claim `Satisfied` here; we
            // fall through to enumerative seeding and ultimately `Unknown`.
            // Generate enumerative instantiations to seed the solver with
            // ground terms (e.g. select(a,0), select(a,1) etc.) so that
            // subsequent rounds have model values for these terms.
            for quantifier in &quantifiers {
                if !quantifier.is_universal || !quantifier.can_instantiate() {
                    continue;
                }
                let engine_insts =
                    self.instantiation_engine
                        .instantiate(quantifier, &completed_model, manager);
                for mut inst in engine_insts {
                    if !self.budget.consume(quantifier.term, 1) {
                        break;
                    }
                    // Simplify the result body so guards like (0 >= 0 /\ 0 <= 3)
                    // collapse to True, and Implies(True, consequent) collapses to
                    // just the consequent.  This produces clean lemmas that the
                    // SAT solver and theory solvers can reason about directly.
                    inst.result = self.deep_simplify(inst.result, manager);
                    // Skip tautologies
                    if manager
                        .get(inst.result)
                        .is_some_and(|t| matches!(t.kind, TermKind::True))
                    {
                        continue;
                    }
                    if !self.is_duplicate(&inst) {
                        self.record_instantiation(&inst);
                        callback.on_instantiation(&inst);
                        all_instantiations.push(inst);
                    }
                }
            }

            if !all_instantiations.is_empty() {
                let result = MBQIResult::NewInstantiations(all_instantiations);
                callback.on_round_end(self.current_round, &result);
                self.update_final_stats();
                return result;
            }

            // Conservatively return Unknown instead of the incorrect Satisfied.
            let result = MBQIResult::Unknown;
            callback.on_round_end(self.current_round, &result);
            self.update_final_stats();
            return result;
        }

        // Step 4: Check instantiation limit
        if self.stats.max_instantiations > 0
            && self.stats.total_instantiations >= self.stats.max_instantiations
        {
            let result = MBQIResult::InstantiationLimit;
            callback.on_round_end(self.current_round, &result);
            self.update_final_stats();
            return result;
        }

        // Return the new instantiations to the solver.
        // The solver will add them as lemmas and re-check SAT.
        // On the next call to MBQI, we'll re-complete the model.
        let result = MBQIResult::NewInstantiations(all_instantiations);
        callback.on_round_end(self.current_round, &result);
        self.update_final_stats();
        result
    }

    /// Build an instantiation lemma by substituting a quantifier's bound
    /// variables with concrete witness terms.
    ///
    /// Substitution is delegated to [`TermManager::substitute`], which handles
    /// **every** `TermKind` (Xor, Distinct, all bit-vector / string /
    /// floating-point operators, nested quantifiers with capture-avoiding
    /// alpha-renaming, ...).  A previous local copy fell through with a
    /// catch-all `_ => term` arm and therefore silently *skipped* substitution
    /// inside those constructs, leaving bound variables in the resulting lemma
    /// -- which, because declared constants share the `TermKind::Var`
    /// representation, could constrain a stray global constant and yield
    /// spurious UNSAT.
    ///
    /// The map is keyed on the interned `(name, sort)` variable term rather
    /// than the bare name, so a constant that merely shares a name but has a
    /// different sort is left untouched.
    ///
    /// Returns `None` when the substituted body still contains one of this
    /// quantifier's bound variables as a *free* occurrence.  That is an
    /// internal error (the substitution failed to reach some position), and
    /// such a lemma must never be emitted.
    fn apply_substitution(
        &self,
        quantifier: &QuantifiedFormula,
        subst: &FxHashMap<Spur, TermId>,
        manager: &mut TermManager,
    ) -> Option<TermId> {
        let mut term_subst: FxHashMap<TermId, TermId> = FxHashMap::default();
        for &(name, sort) in quantifier.bound_vars.iter() {
            if let Some(&value) = subst.get(&name) {
                let name_str = manager.resolve_str(name).to_string();
                let var_id = manager.mk_var(&name_str, sort);
                term_subst.insert(var_id, value);
            }
        }

        if term_subst.is_empty() {
            // Nothing to substitute: the body is already the lemma (this also
            // covers propositional quantifiers with zero bound variables).
            return Some(quantifier.body);
        }

        let result = manager.substitute(quantifier.body, &term_subst);

        // Soundness guard: a free occurrence of any bound variable that we set
        // out to replace means the lemma is not properly grounded.  Reject it
        // rather than emit a lemma that mentions a stray variable.  This is
        // shadowing-aware because `collect_free_vars` respects inner binders,
        // so a nested quantifier legitimately re-binding the same name is not
        // flagged.
        let free = collect_free_vars(result, manager);
        if term_subst.keys().any(|k| free.contains(k)) {
            return None;
        }

        Some(result)
    }

    /// Determine whether every tracked, instantiable quantifier has a body that
    /// simplifies to the constant `true` regardless of its bound variables.
    ///
    /// Such a quantifier (`forall x. body` or `exists x. body` with `body ≡ ⊤`)
    /// is valid over its whole domain — infinite or not — so reporting
    /// `Satisfied` is sound without any finite-domain enumeration.  Returns
    /// `false` when there is no instantiable quantifier, or when any of them has
    /// a body that does not provably collapse to `true`; that keeps the check
    /// conservative (it can only ever *grant* sat for genuine tautologies).
    fn all_quantifiers_trivially_valid(
        &self,
        quantifiers: &[QuantifiedFormula],
        manager: &mut TermManager,
    ) -> bool {
        let mut saw_quantifier = false;
        for quantifier in quantifiers {
            if !quantifier.can_instantiate() {
                continue;
            }
            saw_quantifier = true;
            let simplified = self.deep_simplify(quantifier.body, manager);
            let is_true = manager
                .get(simplified)
                .is_some_and(|t| matches!(t.kind, TermKind::True));
            if !is_true {
                return false;
            }
        }
        saw_quantifier
    }

    /// Determine whether every tracked, instantiable quantifier ranges only
    /// over genuinely finite domains that the counterexample generator
    /// enumerates *exhaustively*.
    ///
    /// This gates the `Satisfied` (sat) result: the counterexample generator
    /// only samples a bounded set of candidate values per bound variable, so
    /// "no counterexample found" is a proof of satisfaction **only** when that
    /// sample covered the entire domain.  Over an infinite domain (Int, Real,
    /// String) or a merely-sampled one (BitVec, large universes), the absence
    /// of a counterexample proves nothing and the honest answer is `Unknown`.
    fn all_domains_finitely_exhausted(
        &self,
        quantifiers: &[QuantifiedFormula],
        model: &CompletedModel,
        manager: &TermManager,
    ) -> bool {
        for quantifier in quantifiers {
            if !quantifier.can_instantiate() {
                continue;
            }
            // Every bound variable must range over a genuinely finite domain
            // AND the *product* of those domain sizes must fit within the
            // generator's per-quantifier combination cap.  The counterexample
            // generator enumerates only the first `COMBINATION_ENUM_CAP` tuples
            // (odometer order, variable 0 fastest) and does not flag the
            // truncation, so a cartesian product larger than the cap would leave
            // some tuples untried -- e.g. `forall x,y,z:U. P` with |U| = 5 has
            // 125 > 100 combinations, and P could be false only at an
            // un-enumerated tuple.  In that case "no counterexample found" does
            // NOT prove satisfaction and we must fall through to `Unknown`.
            let mut product: usize = 1;
            for &(_name, sort) in quantifier.bound_vars.iter() {
                let Some(count) = self.sort_candidate_count(sort, model, manager) else {
                    // Infinite (Int/Real/String) or merely-sampled (BitVec, ...)
                    // domain, or an oversized universe: not exhaustively covered.
                    return false;
                };
                product = product.saturating_mul(count);
                if product > COMBINATION_ENUM_CAP {
                    // The cartesian product exceeds what the generator enumerates;
                    // enumeration was truncated, so absence of a counterexample
                    // proves nothing.
                    return false;
                }
            }
        }
        true
    }

    /// Whether a single sort denotes a finite domain that the counterexample
    /// generator enumerates exhaustively (see [`FINITE_ENUM_LIMIT`]).
    ///
    /// A sort is "finitely exhausted" exactly when
    /// [`sort_candidate_count`](Self::sort_candidate_count) yields a bounded
    /// per-variable candidate count.
    fn sort_finitely_exhausted(
        &self,
        sort: SortId,
        model: &CompletedModel,
        manager: &TermManager,
    ) -> bool {
        self.sort_candidate_count(sort, model, manager).is_some()
    }

    /// Upper bound on the number of distinct candidate values the counterexample
    /// generator enumerates for a bound variable of `sort`, or `None` when the
    /// sort is not exhaustively enumerable (infinite, only sampled, or a
    /// universe larger than [`FINITE_ENUM_LIMIT`]).
    ///
    /// The returned count is a sound *upper* bound on the length of the
    /// per-variable candidate list built by
    /// [`CounterExampleGenerator::build_candidate_lists`](super::counterexample)
    /// (universe elements plus same-sort model values, truncated to
    /// [`FINITE_ENUM_LIMIT`]).  Using an upper bound keeps the product test in
    /// [`all_domains_finitely_exhausted`](Self::all_domains_finitely_exhausted)
    /// conservative: if the bound fits the combination cap, the real enumeration
    /// does too, so no tuple is silently skipped.
    fn sort_candidate_count(
        &self,
        sort: SortId,
        model: &CompletedModel,
        manager: &TermManager,
    ) -> Option<usize> {
        let s = manager.sorts.get(sort)?;
        match &s.kind {
            // Bool has exactly two elements (true / false), both always present
            // in the generator's default candidate list; same-sort model values
            // can only ever be true or false, so the list never exceeds 2.
            SortKind::Bool => Some(2),
            // An uninterpreted sort is finite only when the completed model has
            // pinned a finite universe for it, small enough that every element
            // survives the generator's `FINITE_ENUM_LIMIT` truncation.  The
            // candidate list is `universe ∪ {same-sort model values}` (dupes
            // dropped) truncated to `FINITE_ENUM_LIMIT`; `universe.len() +
            // model-value count` is a sound upper bound on its length.
            SortKind::Uninterpreted(_) => {
                let universe = model.universe(sort)?;
                if universe.is_empty() || universe.len() > FINITE_ENUM_LIMIT {
                    return None;
                }
                let model_values = model
                    .assignments
                    .keys()
                    .filter(|&&term| manager.get(term).is_some_and(|t| t.sort == sort))
                    .count();
                Some(
                    universe
                        .len()
                        .saturating_add(model_values)
                        .min(FINITE_ENUM_LIMIT),
                )
            }
            // Int / Real / String are infinite; BitVec / FloatingPoint /
            // Array / Datatype / parametric sorts are not exhaustively
            // enumerated by the finite candidate sampler.
            _ => None,
        }
    }

    /// Clear the deduplication cache so that fresh instantiations (e.g.
    /// blind or finite domain) with corrected substitution results are
    /// not filtered out as duplicates of earlier results.
    pub fn clear_dedup_cache(&mut self) {
        self.generated_instantiations.clear();
    }

    /// Check if an instantiation is a duplicate
    fn is_duplicate(&self, inst: &Instantiation) -> bool {
        let key = InstantiationKey::from(inst);
        self.generated_instantiations.contains_key(&key)
    }

    /// Record an instantiation
    fn record_instantiation(&mut self, inst: &Instantiation) {
        let key = InstantiationKey::from(inst);
        let count = self.generated_instantiations.entry(key).or_insert(0);
        *count += 1;
        self.stats.total_instantiations += 1;
        self.stats.unique_instantiations = self.generated_instantiations.len();
    }

    /// Check for timeout
    fn check_timeout(&self) -> bool {
        #[cfg(feature = "std")]
        {
            if let (Some(limit), Some(start)) = (self.time_limit, self.start_time) {
                return start.elapsed() >= limit;
            }
        }
        false
    }

    /// Update final statistics
    fn update_final_stats(&mut self) {
        #[cfg(feature = "std")]
        if let Some(start) = self.start_time {
            self.stats.total_time_us = start.elapsed().as_micros() as u64;
        }
    }

    /// Clear all state
    pub fn clear(&mut self) {
        self.quantifiers.clear();
        self.generated_instantiations.clear();
        self.extra_candidates.clear();
        self.blind_attempted = false;
        self.current_round = 0;
        self.budget = MBQIBudget::new(self.budget.global_budget);
        self.conflict_scores = ConflictScores::new(self.conflict_scores.decay_factor);
        #[cfg(feature = "std")]
        {
            self.start_time = None;
        }
        self.instantiation_engine.clear_caches();
        self.lazy_instantiator.clear();
    }

    /// Collect ground terms from a trigger pattern and seed them as MBQI
    /// instantiation candidates.
    ///
    /// A trigger such as `f(x, g(0))` is a bare subterm lifted out of the
    /// enclosing `forall`/`exists`, so this function has no access to which
    /// `TermKind::Var` occurrences are the quantifier's bound variables
    /// (bound variables and declared constants share the same `Var`
    /// representation; see `Self::apply_substitution`). To stay sound
    /// without that context, a subterm is only registered when its entire
    /// subtree contains **no** `Var` node at all -- i.e. it is a genuinely
    /// closed/ground term (numeric and other literals, and applications
    /// built purely from such literals, e.g. `g(0)`). Such terms evaluate to
    /// the same value under every model and are always safe instantiation
    /// candidates. Declared free constants are seeded separately via
    /// [`Self::register_declared_const`].
    pub fn collect_ground_terms(&mut self, term: TermId, manager: &TermManager) {
        // `collect_subterms` returns every subterm (including `term` itself)
        // in post-order, so children are visited before their parents and a
        // single forward pass can compute groundness bottom-up.
        let subterms = oxiz_core::ast::traversal::collect_subterms(term, manager);
        let mut is_ground: FxHashMap<TermId, bool> = FxHashMap::default();

        for &sub in &subterms {
            let Some(t) = manager.get(sub) else {
                is_ground.insert(sub, false);
                continue;
            };
            let ground = if matches!(t.kind, TermKind::Var(_)) {
                false
            } else {
                oxiz_core::ast::traversal::get_children(&t.kind)
                    .iter()
                    .all(|c| is_ground.get(c).copied().unwrap_or(false))
            };
            is_ground.insert(sub, ground);

            if ground {
                self.add_candidate(sub, t.sort);
            }
        }
    }

    /// Check quantifiers with a given model
    pub fn check_with_model(
        &mut self,
        model: &FxHashMap<TermId, TermId>,
        manager: &mut TermManager,
    ) -> MBQIResult {
        // Use a no-op callback for this convenience method
        #[derive(Debug)]
        struct NoOpCallback;
        impl SolverCallback for NoOpCallback {
            fn on_instantiation(&mut self, _: &Instantiation) {}
            fn on_round_start(&mut self, _: usize) {}
            fn on_round_end(&mut self, _: usize, _: &MBQIResult) {}
            fn on_conflict(&mut self, _: TermId, _: &[TermId]) {}
            fn should_stop(&self) -> bool {
                false
            }
        }
        let mut callback = NoOpCallback;
        self.run(model, manager, &mut callback)
    }

    /// Get statistics
    pub fn stats(&self) -> &MBQIStats {
        &self.stats
    }

    /// Set maximum rounds
    pub fn set_max_rounds(&mut self, max: usize) {
        self.max_rounds = max;
    }

    /// Set time limit
    #[cfg(feature = "std")]
    pub fn set_time_limit(&mut self, limit: Duration) {
        self.time_limit = Some(limit);
    }

    /// Add a candidate term for model-based instantiation.
    ///
    /// The term is stored per-sort and will be injected into candidate lists
    /// when the counterexample generator builds domain enumerations.
    pub fn add_candidate(&mut self, term: TermId, sort: SortId) {
        self.extra_candidates.entry(sort).or_default().push(term);
    }

    /// Whether blind instantiation has been attempted
    pub fn blind_tried(&self) -> bool {
        self.blind_attempted
    }

    /// Mark blind instantiation as attempted
    pub fn mark_blind_tried(&mut self) {
        self.blind_attempted = true;
    }

    /// Check if MBQI is enabled
    pub fn is_enabled(&self) -> bool {
        // MBQI is always enabled when the struct exists
        true
    }

    /// Register a ground constant as an instantiation candidate.
    ///
    /// Called from the context layer whenever a `declare-const` is processed.
    /// The constant is forwarded to `add_candidate` so that trigger-free
    /// quantifiers can be instantiated with it.
    pub fn register_declared_const(&mut self, term: TermId, sort: SortId) {
        self.add_candidate(term, sort);
    }

    /// Attempt to produce trivial instantiations for trigger-free quantifiers.
    ///
    /// Returns the list of resulting [`Instantiation`]s.  Returns an empty vec
    /// when no quantifiers are registered, no candidates exist, or all
    /// quantifiers have trigger patterns that are handled by E-matching.
    ///
    /// The full ground-term enumeration strategy is implemented in the main
    /// MBQI engine; this method is an escape valve for the `Unknown` case.
    pub fn try_trivial_instantiation(&mut self, _manager: &mut TermManager) -> Vec<Instantiation> {
        Vec::new()
    }

    /// Generate "blind" instantiations for all universal quantifiers.
    ///
    /// Unlike the normal MBQI flow (which checks counterexamples against the
    /// model), this method instantiates every universal quantifier with every
    /// Generate instantiations by detecting finite integer domains in
    /// quantifier guards and enumerating all values.  For a guard like
    /// `(>= i 0) && (<= i 3)`, this generates instances for i=0,1,2,3.
    /// Unlike `generate_blind_instantiations` which uses a fixed range,
    /// this extracts the exact bounds from the formula.
    pub fn generate_finite_domain_instantiations(
        &mut self,
        manager: &mut TermManager,
    ) -> Vec<Instantiation> {
        use num_bigint::BigInt;
        let mut all_insts = Vec::new();
        let quantifiers: Vec<_> = self.quantifiers.to_vec();

        for quantifier in &quantifiers {
            if !quantifier.is_universal || !quantifier.can_instantiate() {
                continue;
            }

            // Try to extract integer bounds for each variable from the body
            let bounds = self.extract_variable_bounds(quantifier, manager);
            if bounds.is_empty() {
                continue;
            }

            // Build candidate lists from the extracted bounds
            let mut candidate_lists: Vec<Vec<TermId>> = Vec::new();
            for &(var_name, sort) in &quantifier.bound_vars {
                if let Some(&(lo, hi)) = bounds.get(&var_name) {
                    if hi - lo <= 20 && sort == manager.sorts.int_sort {
                        let cands: Vec<TermId> =
                            (lo..=hi).map(|v| manager.mk_int(BigInt::from(v))).collect();
                        candidate_lists.push(cands);
                    } else {
                        // Too large or non-int: add defaults
                        let mut cands = Vec::new();
                        if sort == manager.sorts.int_sort {
                            for i in -2i64..=5 {
                                cands.push(manager.mk_int(BigInt::from(i)));
                            }
                        }
                        candidate_lists.push(cands);
                    }
                } else {
                    let mut cands = Vec::new();
                    if sort == manager.sorts.int_sort {
                        for i in -2i64..=5 {
                            cands.push(manager.mk_int(BigInt::from(i)));
                        }
                    }
                    candidate_lists.push(cands);
                }
            }

            if candidate_lists.is_empty() || candidate_lists.iter().any(|c| c.is_empty()) {
                continue;
            }
            let combos = self.enumerate_combinations_blind(&candidate_lists, 2000);
            for combo in combos {
                let mut subst = FxHashMap::default();
                for (i, &val) in combo.iter().enumerate() {
                    if let Some(var_name) = quantifier.var_name(i) {
                        subst.insert(var_name, val);
                    }
                }
                let Some(ground_body) = self.apply_substitution(quantifier, &subst, manager) else {
                    // Internal error: substitution left a free bound variable.
                    continue;
                };
                let inst = Instantiation::new(
                    quantifier.term,
                    subst,
                    ground_body,
                    self.current_round as u32,
                );
                if !self.is_duplicate(&inst) {
                    self.record_instantiation(&inst);
                    all_insts.push(inst);
                }
            }
        }
        all_insts
    }

    /// Extract integer bounds for quantifier variables from the body.
    /// Looks for patterns like `(=> (and (>= i 0) (<= i 3) ...) body)`
    /// Extract integer bounds for quantifier variables from the body.
    /// Looks for patterns like `(=> (and (>= i 0) (<= i 3) ...) body)`
    fn extract_variable_bounds(
        &self,
        quantifier: &QuantifiedFormula,
        manager: &TermManager,
    ) -> FxHashMap<Spur, (i64, i64)> {
        use num_traits::ToPrimitive;
        let mut bounds: FxHashMap<Spur, (i64, i64)> = FxHashMap::default();
        let Some(t) = manager.get(quantifier.body) else {
            return bounds;
        };

        // Look for Implies(guard, consequent) pattern
        let guard = match &t.kind {
            TermKind::Implies(guard, _) => *guard,
            _ => return bounds,
        };

        let Some(gt) = manager.get(guard) else {
            return bounds;
        };

        let args = match &gt.kind {
            TermKind::And(args) => args.clone(),
            _ => return bounds,
        };

        // Collect per-variable bounds from Ge/Le
        let mut lowers: FxHashMap<Spur, i64> = FxHashMap::default();
        let mut uppers: FxHashMap<Spur, i64> = FxHashMap::default();

        for &a in args.iter() {
            let Some(at) = manager.get(a) else { continue };
            match &at.kind {
                TermKind::Ge(lhs, rhs) => {
                    if let (Some(lt), Some(rt)) = (manager.get(*lhs), manager.get(*rhs)) {
                        if let (TermKind::Var(name), TermKind::IntConst(n)) = (&lt.kind, &rt.kind) {
                            if let Some(v) = n.to_i64() {
                                lowers
                                    .entry(*name)
                                    .and_modify(|e| *e = (*e).max(v))
                                    .or_insert(v);
                            }
                        }
                    }
                }
                TermKind::Le(lhs, rhs) => {
                    if let (Some(lt), Some(rt)) = (manager.get(*lhs), manager.get(*rhs)) {
                        if let (TermKind::Var(name), TermKind::IntConst(n)) = (&lt.kind, &rt.kind) {
                            if let Some(v) = n.to_i64() {
                                uppers
                                    .entry(*name)
                                    .and_modify(|e| *e = (*e).min(v))
                                    .or_insert(v);
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        for (&name, &lo) in &lowers {
            if let Some(&hi) = uppers.get(&name) {
                if hi >= lo {
                    bounds.insert(name, (lo, hi));
                }
            }
        }

        bounds
    }

    /// combination of candidate values and returns the ground lemmas.  The
    /// caller adds them directly to the SAT solver so that theory solvers can
    /// detect contradictions (e.g. pigeonhole, Skolem contradictions).
    pub fn generate_blind_instantiations(
        &mut self,
        manager: &mut TermManager,
    ) -> Vec<Instantiation> {
        use num_bigint::BigInt;

        let mut all_insts = Vec::new();
        let quantifiers: Vec<_> = self.quantifiers.to_vec();

        for quantifier in &quantifiers {
            if !quantifier.is_universal || !quantifier.can_instantiate() {
                continue;
            }

            // Build candidate lists for each bound variable
            let mut candidate_lists: Vec<Vec<TermId>> = Vec::new();
            for &(_var_name, sort) in &quantifier.bound_vars {
                let mut cands = Vec::new();

                // Include extra candidates (Skolem terms, etc.)
                if let Some(extras) = self.extra_candidates.get(&sort) {
                    for &t in extras {
                        if !cands.contains(&t) {
                            cands.push(t);
                        }
                    }
                }

                // Add default integer candidates
                if sort == manager.sorts.int_sort {
                    for i in -2i64..=5 {
                        let val = manager.mk_int(BigInt::from(i));
                        if !cands.contains(&val) {
                            cands.push(val);
                        }
                    }
                } else if sort == manager.sorts.bool_sort {
                    let t_val = manager.mk_true();
                    let f_val = manager.mk_false();
                    if !cands.contains(&t_val) {
                        cands.push(t_val);
                    }
                    if !cands.contains(&f_val) {
                        cands.push(f_val);
                    }
                }

                // Limit per variable
                cands.truncate(16);
                candidate_lists.push(cands);
            }

            if candidate_lists.is_empty() {
                continue;
            }

            // Enumerate combinations
            let combos = self.enumerate_combinations_blind(&candidate_lists, 500);
            for combo in combos {
                // Build substitution
                let mut subst = FxHashMap::default();
                for (i, &val) in combo.iter().enumerate() {
                    if let Some(var_name) = quantifier.var_name(i) {
                        subst.insert(var_name, val);
                    }
                }

                let Some(ground_body) = self.apply_substitution(quantifier, &subst, manager) else {
                    // Internal error: substitution left a free bound variable.
                    continue;
                };
                // Simplify arithmetic comparisons of constants (e.g. 0 >= 0 → True)
                // and boolean simplifications so the SAT solver sees clean lemmas.
                let simplified = self.deep_simplify(ground_body, manager);

                // Skip tautologies (body simplifies to True — no information)
                if manager
                    .get(simplified)
                    .is_some_and(|t| matches!(t.kind, TermKind::True))
                {
                    continue;
                }

                // Skip lemmas that still have an Implies at the top level
                // after simplification. These have non-ground guards (free
                // variables from declared constants) and can cause spurious
                // UNSAT when the theory solver doesn't handle them correctly.
                // Lemmas with fully resolved guards collapse to just the
                // consequent (no Implies wrapper) and are safe to add.
                if manager
                    .get(simplified)
                    .is_some_and(|t| matches!(t.kind, TermKind::Implies(_, _)))
                {
                    continue;
                }

                let inst = Instantiation::new(quantifier.term, subst, simplified, 0);

                if !self.is_duplicate(&inst) {
                    self.record_instantiation(&inst);
                    all_insts.push(inst);
                }
            }
        }

        all_insts
    }

    /// Deep-simplify a ground term: reduce constant comparisons, propagate
    /// boolean values through And/Or/Implies/Not, etc.
    pub fn deep_simplify(&self, term: TermId, manager: &mut TermManager) -> TermId {
        let mut cache = FxHashMap::default();
        self.deep_simplify_cached(term, manager, &mut cache)
    }

    fn deep_simplify_cached(
        &self,
        term: TermId,
        manager: &mut TermManager,
        cache: &mut FxHashMap<TermId, TermId>,
    ) -> TermId {
        if let Some(&c) = cache.get(&term) {
            return c;
        }
        let Some(t) = manager.get(term).cloned() else {
            return term;
        };
        let result = match &t.kind {
            TermKind::True
            | TermKind::False
            | TermKind::IntConst(_)
            | TermKind::RealConst(_)
            | TermKind::BitVecConst { .. }
            | TermKind::StringLit(_)
            | TermKind::Var(_) => term,

            TermKind::Not(a) => {
                let sa = self.deep_simplify_cached(*a, manager, cache);
                match manager.get(sa).map(|t2| &t2.kind) {
                    Some(TermKind::True) => manager.mk_false(),
                    Some(TermKind::False) => manager.mk_true(),
                    _ => manager.mk_not(sa),
                }
            }
            TermKind::And(args) => {
                let mut simplified = Vec::new();
                for &a in args.iter() {
                    let sa = self.deep_simplify_cached(a, manager, cache);
                    match manager.get(sa).map(|t2| &t2.kind) {
                        Some(TermKind::False) => {
                            return {
                                let r = manager.mk_false();
                                cache.insert(term, r);
                                r
                            };
                        }
                        Some(TermKind::True) => { /* skip */ }
                        _ => simplified.push(sa),
                    }
                }
                if simplified.is_empty() {
                    manager.mk_true()
                } else if simplified.len() == 1 {
                    simplified[0]
                } else {
                    manager.mk_and(simplified)
                }
            }
            TermKind::Or(args) => {
                let mut simplified = Vec::new();
                for &a in args.iter() {
                    let sa = self.deep_simplify_cached(a, manager, cache);
                    match manager.get(sa).map(|t2| &t2.kind) {
                        Some(TermKind::True) => {
                            return {
                                let r = manager.mk_true();
                                cache.insert(term, r);
                                r
                            };
                        }
                        Some(TermKind::False) => { /* skip */ }
                        _ => simplified.push(sa),
                    }
                }
                if simplified.is_empty() {
                    manager.mk_false()
                } else if simplified.len() == 1 {
                    simplified[0]
                } else {
                    manager.mk_or(simplified)
                }
            }
            TermKind::Implies(lhs, rhs) => {
                let sl = self.deep_simplify_cached(*lhs, manager, cache);
                let sr = self.deep_simplify_cached(*rhs, manager, cache);
                match manager.get(sl).map(|t2| &t2.kind) {
                    Some(TermKind::False) => manager.mk_true(),
                    Some(TermKind::True) => sr,
                    _ => match manager.get(sr).map(|t2| &t2.kind) {
                        Some(TermKind::True) => manager.mk_true(),
                        _ => manager.mk_implies(sl, sr),
                    },
                }
            }
            TermKind::Eq(lhs, rhs) => {
                let sl = self.deep_simplify_cached(*lhs, manager, cache);
                let sr = self.deep_simplify_cached(*rhs, manager, cache);
                self.simplify_eq(sl, sr, manager)
            }
            TermKind::Le(lhs, rhs) => {
                let sl = self.deep_simplify_cached(*lhs, manager, cache);
                let sr = self.deep_simplify_cached(*rhs, manager, cache);
                self.simplify_le(sl, sr, manager)
            }
            TermKind::Lt(lhs, rhs) => {
                let sl = self.deep_simplify_cached(*lhs, manager, cache);
                let sr = self.deep_simplify_cached(*rhs, manager, cache);
                self.simplify_lt(sl, sr, manager)
            }
            TermKind::Ge(lhs, rhs) => {
                let sl = self.deep_simplify_cached(*lhs, manager, cache);
                let sr = self.deep_simplify_cached(*rhs, manager, cache);
                self.simplify_le(sr, sl, manager) // a >= b ≡ b <= a
            }
            TermKind::Gt(lhs, rhs) => {
                let sl = self.deep_simplify_cached(*lhs, manager, cache);
                let sr = self.deep_simplify_cached(*rhs, manager, cache);
                self.simplify_lt(sr, sl, manager) // a > b ≡ b < a
            }
            TermKind::Select(arr, idx) => {
                let sa = self.deep_simplify_cached(*arr, manager, cache);
                let si = self.deep_simplify_cached(*idx, manager, cache);
                manager.mk_select(sa, si)
            }
            TermKind::Apply { func, args } => {
                let fname = manager.resolve_str(*func).to_string();
                let new_args: SmallVec<[TermId; 4]> = args
                    .iter()
                    .map(|&a| self.deep_simplify_cached(a, manager, cache))
                    .collect();
                manager.mk_apply(&fname, new_args, t.sort)
            }
            _ => term,
        };
        cache.insert(term, result);
        result
    }

    /// Simplify `lhs = rhs` when both are integer constants
    fn simplify_eq(&self, lhs: TermId, rhs: TermId, manager: &mut TermManager) -> TermId {
        if lhs == rhs {
            return manager.mk_true();
        }
        let l = manager.get(lhs).cloned();
        let r = manager.get(rhs).cloned();
        if let (Some(lt), Some(rt)) = (l, r) {
            if let (TermKind::IntConst(a), TermKind::IntConst(b)) = (&lt.kind, &rt.kind) {
                return if a == b {
                    manager.mk_true()
                } else {
                    manager.mk_false()
                };
            }
        }
        manager.mk_eq(lhs, rhs)
    }

    /// Simplify `lhs <= rhs` when both are integer constants
    fn simplify_le(&self, lhs: TermId, rhs: TermId, manager: &mut TermManager) -> TermId {
        let l = manager.get(lhs).cloned();
        let r = manager.get(rhs).cloned();
        if let (Some(lt), Some(rt)) = (l, r) {
            if let (TermKind::IntConst(a), TermKind::IntConst(b)) = (&lt.kind, &rt.kind) {
                return if a <= b {
                    manager.mk_true()
                } else {
                    manager.mk_false()
                };
            }
        }
        manager.mk_le(lhs, rhs)
    }

    /// Simplify `lhs < rhs` when both are integer constants
    fn simplify_lt(&self, lhs: TermId, rhs: TermId, manager: &mut TermManager) -> TermId {
        let l = manager.get(lhs).cloned();
        let r = manager.get(rhs).cloned();
        if let (Some(lt), Some(rt)) = (l, r) {
            if let (TermKind::IntConst(a), TermKind::IntConst(b)) = (&lt.kind, &rt.kind) {
                return if a < b {
                    manager.mk_true()
                } else {
                    manager.mk_false()
                };
            }
        }
        manager.mk_lt(lhs, rhs)
    }

    /// Enumerate all combinations up to a maximum total count.
    fn enumerate_combinations_blind(
        &self,
        candidates: &[Vec<TermId>],
        max_total: usize,
    ) -> Vec<Vec<TermId>> {
        if candidates.is_empty() {
            return vec![vec![]];
        }

        let mut results = Vec::new();
        let mut indices = vec![0usize; candidates.len()];

        loop {
            let combo: Vec<TermId> = indices
                .iter()
                .enumerate()
                .filter_map(|(i, &idx)| candidates.get(i).and_then(|c| c.get(idx).copied()))
                .collect();

            if combo.len() == candidates.len() {
                results.push(combo);
            }

            if results.len() >= max_total {
                break;
            }

            // Increment indices (odometer style)
            let mut carry = true;
            for (i, idx) in indices.iter_mut().enumerate() {
                if carry {
                    *idx += 1;
                    let limit = candidates.get(i).map_or(1, |c| c.len());
                    if *idx >= limit {
                        *idx = 0;
                    } else {
                        carry = false;
                    }
                }
            }

            if carry {
                break;
            }
        }

        results
    }
}

impl Default for MBQIIntegration {
    fn default() -> Self {
        Self::new()
    }
}

/// Key for instantiation deduplication
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct InstantiationKey {
    quantifier: TermId,
    binding: Vec<(oxiz_core::interner::Spur, TermId)>,
}

impl From<&Instantiation> for InstantiationKey {
    fn from(inst: &Instantiation) -> Self {
        let mut binding: Vec<_> = inst.substitution.iter().map(|(&k, &v)| (k, v)).collect();
        binding.sort_by_key(|(k, _)| *k);
        Self {
            quantifier: inst.quantifier,
            binding,
        }
    }
}

/// Default callback implementation (no-op)
#[derive(Debug)]
pub struct DefaultCallback {
    stop_requested: bool,
}

impl DefaultCallback {
    pub fn new() -> Self {
        Self {
            stop_requested: false,
        }
    }

    pub fn request_stop(&mut self) {
        self.stop_requested = true;
    }
}

impl Default for DefaultCallback {
    fn default() -> Self {
        Self::new()
    }
}

impl SolverCallback for DefaultCallback {
    fn on_instantiation(&mut self, _inst: &Instantiation) {}
    fn on_conflict(&mut self, _quantifier: TermId, _reason: &[TermId]) {}
    fn on_round_start(&mut self, _round: usize) {}
    fn on_round_end(&mut self, _round: usize, _result: &MBQIResult) {}
    fn should_stop(&self) -> bool {
        self.stop_requested
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mbqi_integration_creation() {
        let integration = MBQIIntegration::new();
        assert_eq!(integration.quantifiers.len(), 0);
        assert_eq!(integration.current_round, 0);
    }

    #[test]
    fn test_default_callback() {
        let mut callback = DefaultCallback::new();
        assert!(!callback.should_stop());
        callback.request_stop();
        assert!(callback.should_stop());
    }

    #[test]
    fn test_integration_clear() {
        let mut integration = MBQIIntegration::new();
        integration.current_round = 5;
        integration.clear();
        assert_eq!(integration.current_round, 0);
        assert_eq!(integration.quantifiers.len(), 0);
    }

    #[test]
    fn test_set_max_rounds() {
        let mut integration = MBQIIntegration::new();
        integration.set_max_rounds(50);
        assert_eq!(integration.max_rounds, 50);
    }

    /// Regression test for the audit finding that `set_max_rounds` was
    /// ineffective: `run()` used to reset `current_round` to `0` on every
    /// call, so `current_round >= max_rounds` could never fire (barring
    /// `max_rounds == 0`). `run()` is invoked once per outer solver
    /// iteration (see `check_with_model`, called from `solver::mod::solve`),
    /// so `current_round` must accumulate *across* calls for the limit to
    /// bound the total number of MBQI rounds for a single solve.
    #[test]
    fn test_audit_max_rounds_accumulates_and_is_enforced() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let zero = manager.mk_int(0);
        // `forall x. f(x) > 0` over the infinite Int domain: neither
        // trivially valid nor finitely exhaustible, so successive `run()`
        // calls never resolve to `Satisfied` and keep consuming rounds.
        let f_x = manager.mk_apply("f", [x], int_sort);
        let body = manager.mk_gt(f_x, zero);
        let forall = manager.mk_forall([("x", int_sort)], body);

        let mut integration = MBQIIntegration::new();
        integration.add_quantifier(forall, &manager);
        integration.set_max_rounds(2);

        let model = FxHashMap::default();
        for _ in 0..2 {
            let _ = integration.check_with_model(&model, &mut manager);
        }
        assert_eq!(
            integration.current_round, 2,
            "current_round must persist/accumulate across calls, not reset to 0 each run()"
        );

        // A further call must now be refused purely on the round limit,
        // without incrementing current_round any further.
        let result = integration.check_with_model(&model, &mut manager);
        assert!(
            matches!(result, MBQIResult::Unknown),
            "expected Unknown once max_rounds is exhausted, got {result:?}"
        );
        assert_eq!(
            integration.current_round, 2,
            "run() must return before incrementing once the round limit is hit"
        );
    }

    #[test]
    fn test_set_time_limit() {
        let mut integration = MBQIIntegration::new();
        let limit = Duration::from_secs(30);
        integration.set_time_limit(limit);
        assert_eq!(integration.time_limit, Some(limit));
    }

    /// Regression test for the audit finding that `collect_ground_terms`
    /// was an empty stub: trigger patterns never seeded candidates.
    /// A trigger `g(0)` (fully ground: no `Var` anywhere in its subtree)
    /// must now register both `g(0)` itself and the literal `0` as
    /// candidates for their respective sorts, while a trigger containing a
    /// bound variable (`f(x)`) must register nothing, since `f(x)` is not
    /// ground under any binder-free interpretation.
    #[test]
    fn test_audit_collect_ground_terms_seeds_candidates() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;

        let zero = manager.mk_int(0);
        let g_zero = manager.mk_apply("g", [zero], int_sort);

        let mut integration = MBQIIntegration::new();
        integration.collect_ground_terms(g_zero, &manager);

        let candidates = integration
            .extra_candidates
            .get(&int_sort)
            .cloned()
            .unwrap_or_default();
        assert!(
            candidates.contains(&g_zero),
            "the fully ground trigger term itself must be seeded as a candidate"
        );
        assert!(
            candidates.contains(&zero),
            "ground subterms of the trigger must also be seeded as candidates"
        );

        // A trigger containing a `Var` occurrence anywhere (e.g. the bound
        // variable `x` of the enclosing quantifier) must not add any new
        // candidates: it isn't ground.
        let mut integration2 = MBQIIntegration::new();
        let x = manager.mk_var("x", int_sort);
        let f_x = manager.mk_apply("f", [x], int_sort);
        integration2.collect_ground_terms(f_x, &manager);
        assert!(
            integration2.extra_candidates.is_empty(),
            "a trigger containing a Var occurrence must not be treated as ground"
        );
    }

    // ---------------------------------------------------------------------
    // Audit regression tests (solver-mbqi)
    // ---------------------------------------------------------------------

    use num_bigint::BigInt;

    /// Finding #1 (integration.rs:296): a universal quantifier over the
    /// *infinite* Int domain must NEVER be reported `Satisfied` (sat) merely
    /// because a finite sample of candidate values did not falsify it.
    ///
    /// `(forall ((x Int)) (>= x (- 10)))` is false at `x = -11`, yet the finite
    /// candidate sampler only tries roughly `-2..=5`, all of which satisfy the
    /// body.  The result must be non-sat (Unknown / instantiations), never
    /// Satisfied.
    #[test]
    fn test_audit_infinite_int_domain_not_satisfied() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let neg_ten = manager.mk_int(BigInt::from(-10));
        let body = manager.mk_ge(x, neg_ten);
        let forall = manager.mk_forall([("x", int_sort)], body);

        let mut integration = MBQIIntegration::new();
        integration.add_quantifier(forall, &manager);

        let model = FxHashMap::default();
        let result = integration.check_with_model(&model, &mut manager);
        assert!(
            !result.is_sat(),
            "forall x:Int. x >= -10 is false at x=-11 and must NOT be reported \
             Satisfied from a finite candidate sample, got {result:?}"
        );
    }

    /// Finding #1: classification of which sorts the counterexample generator
    /// can enumerate exhaustively.  Bool is exhaustible; Int/Real/String are
    /// not (infinite); BitVec is not (only sampled).
    #[test]
    fn test_audit_sort_finitely_exhausted_classification() {
        let mut manager = TermManager::new();
        let integration = MBQIIntegration::new();
        let model = CompletedModel::new();

        let bool_sort = manager.sorts.bool_sort;
        let int_sort = manager.sorts.int_sort;
        let real_sort = manager.sorts.real_sort;
        let bv_sort = manager.sorts.bitvec(8);

        assert!(
            integration.sort_finitely_exhausted(bool_sort, &model, &manager),
            "Bool is a genuinely finite, fully-enumerated domain"
        );
        assert!(
            !integration.sort_finitely_exhausted(int_sort, &model, &manager),
            "Int is infinite and must not be treated as exhausted"
        );
        assert!(
            !integration.sort_finitely_exhausted(real_sort, &model, &manager),
            "Real is infinite and must not be treated as exhausted"
        );
        assert!(
            !integration.sort_finitely_exhausted(bv_sort, &model, &manager),
            "BitVec is only sampled, never fully enumerated by the candidate sampler"
        );
    }

    /// Finding #1: an uninterpreted sort is exhaustible only when the completed
    /// model pins a small finite universe for it.  A universe larger than the
    /// candidate limit is NOT fully enumerated.
    #[test]
    fn test_audit_uninterpreted_universe_exhaustion() {
        let mut manager = TermManager::new();
        let integration = MBQIIntegration::new();

        let spur = manager.intern_str("U");
        let u_sort = manager.sorts.intern(SortKind::Uninterpreted(spur));

        // No universe at all -> not exhausted.
        let empty_model = CompletedModel::new();
        assert!(!integration.sort_finitely_exhausted(u_sort, &empty_model, &manager));

        // Small universe (<= FINITE_ENUM_LIMIT) -> exhausted.
        let mut small_model = CompletedModel::new();
        for i in 0..3i64 {
            let v = manager.mk_int(BigInt::from(i));
            small_model.add_to_universe(u_sort, v);
        }
        assert!(
            integration.sort_finitely_exhausted(u_sort, &small_model, &manager),
            "a 3-element universe fits within FINITE_ENUM_LIMIT and is exhausted"
        );

        // Oversized universe (> FINITE_ENUM_LIMIT) -> not exhausted, because the
        // sampler truncates the candidate list and would miss elements.
        let mut big_model = CompletedModel::new();
        for i in 0..(FINITE_ENUM_LIMIT as i64 + 5) {
            let v = manager.mk_int(BigInt::from(i));
            big_model.add_to_universe(u_sort, v);
        }
        assert!(
            !integration.sort_finitely_exhausted(u_sort, &big_model, &manager),
            "a universe larger than FINITE_ENUM_LIMIT is not fully enumerated"
        );
    }

    /// Finding #1 (reviewer follow-up): the finite-domain gate must account for
    /// the counterexample generator's *cartesian-product* enumeration cap, not
    /// just per-variable finiteness.  `forall x,y,z : U. P` with a completed
    /// model pinning |U| = 5 has 125 candidate tuples, but the generator
    /// enumerates only the first `COMBINATION_ENUM_CAP` (= 100) and does not
    /// flag the truncation.  Because P could be false only at an un-enumerated
    /// tuple, the absence of a counterexample must NOT be reported `Satisfied`.
    #[test]
    fn test_audit_multivar_product_exceeds_combination_cap_not_exhausted() {
        let mut manager = TermManager::new();
        let spur = manager.intern_str("U");
        let u_sort = manager.sorts.intern(SortKind::Uninterpreted(spur));

        // Completed model with a 5-element universe for U.
        let mut model = CompletedModel::new();
        for i in 0..5i64 {
            let v = manager.mk_int(BigInt::from(i));
            model.add_to_universe(u_sort, v);
        }

        let build = |manager: &mut TermManager, n: usize| {
            let vars: Vec<(&str, SortId)> = ["x", "y", "z"][..n]
                .iter()
                .map(|&nm| (nm, u_sort))
                .collect();
            let body = manager.mk_true();
            let forall = manager.mk_forall(vars, body);
            let mut integration = MBQIIntegration::new();
            integration.add_quantifier(forall, manager);
            integration.quantifiers.clone()
        };

        let integration = MBQIIntegration::new();

        // 2 variables -> 5*5 = 25 <= 100: fully enumerated, may conclude sat.
        let q2 = build(&mut manager, 2);
        assert!(
            integration.all_domains_finitely_exhausted(&q2, &model, &manager),
            "2 vars over |U|=5 has 25 combinations (<= cap) and IS fully enumerated"
        );

        // 3 variables -> 5*5*5 = 125 > 100: truncated, must NOT conclude sat.
        let q3 = build(&mut manager, 3);
        assert!(
            !integration.all_domains_finitely_exhausted(&q3, &model, &manager),
            "3 vars over |U|=5 has 125 combinations (> cap); enumeration is \
             truncated so the domain is NOT exhaustively covered and MBQI must \
             not report Satisfied"
        );
    }

    /// Finding #1 (reviewer follow-up): a large number of Bool-quantified
    /// variables also blows past the combination cap (2^n grows quickly), so
    /// such a quantifier must not be treated as exhaustively enumerated even
    /// though each individual Bool domain is trivially finite.
    #[test]
    fn test_audit_many_bool_vars_exceed_combination_cap() {
        let mut manager = TermManager::new();
        let bool_sort = manager.sorts.bool_sort;
        let model = CompletedModel::new();

        let build = |manager: &mut TermManager, n: usize| {
            let names = ["a", "b", "c", "d", "e", "f", "g", "h"];
            let vars: Vec<(&str, SortId)> = names[..n].iter().map(|&nm| (nm, bool_sort)).collect();
            let body = manager.mk_true();
            let forall = manager.mk_forall(vars, body);
            let mut integration = MBQIIntegration::new();
            integration.add_quantifier(forall, manager);
            integration.quantifiers.clone()
        };

        let integration = MBQIIntegration::new();

        // 6 Bool vars -> 2^6 = 64 <= 100: fully enumerated.
        let q6 = build(&mut manager, 6);
        assert!(
            integration.all_domains_finitely_exhausted(&q6, &model, &manager),
            "2^6 = 64 combinations fit within the cap"
        );

        // 7 Bool vars -> 2^7 = 128 > 100: truncated, not exhausted.
        let q7 = build(&mut manager, 7);
        assert!(
            !integration.all_domains_finitely_exhausted(&q7, &model, &manager),
            "2^7 = 128 combinations exceed the cap and are not fully enumerated"
        );
    }

    /// Finding #2 (integration.rs:509): substitution must descend into EVERY
    /// term kind, including `Xor`.  Previously the catch-all `_ => term` arm
    /// skipped `Xor`, leaving the bound variable `x` inside `(xor x false)`
    /// even after instantiating `x := true` -- producing a lemma that
    /// constrains a stray free variable.
    #[test]
    fn test_audit_substitution_covers_xor_no_leftover_bound_var() {
        let mut manager = TermManager::new();
        let bool_sort = manager.sorts.bool_sort;
        let x = manager.mk_var("x", bool_sort);
        let f = manager.mk_false();
        let xor = manager.mk_xor(x, f);
        let body = manager.mk_eq(x, xor); // (= x (xor x false))
        let forall = manager.mk_forall([("x", bool_sort)], body);

        let mut integration = MBQIIntegration::new();
        integration.add_quantifier(forall, &manager);
        let quantifier = integration.quantifiers[0].clone();

        let true_val = manager.mk_true();
        let x_spur = quantifier.bound_vars[0].0;
        let mut subst: FxHashMap<Spur, TermId> = FxHashMap::default();
        subst.insert(x_spur, true_val);

        let result = integration
            .apply_substitution(&quantifier, &subst, &mut manager)
            .expect("substitution of x:=true must fully ground the Xor body");

        let free = collect_free_vars(result, &manager);
        assert!(
            !free.contains(&x),
            "instantiation lemma still contains free bound variable x -- Xor was \
             not substituted (found free vars: {free:?})"
        );
    }

    /// Finding #2: substitution must descend into `Distinct` (also previously
    /// skipped by the catch-all arm).
    #[test]
    fn test_audit_substitution_covers_distinct() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let c0 = manager.mk_int(BigInt::from(0));
        let c1 = manager.mk_int(BigInt::from(1));
        let distinct = manager.mk_distinct([x, c0, c1]); // (distinct x 0 1)
        let forall = manager.mk_forall([("x", int_sort)], distinct);

        let mut integration = MBQIIntegration::new();
        integration.add_quantifier(forall, &manager);
        let quantifier = integration.quantifiers[0].clone();

        let seven = manager.mk_int(BigInt::from(7));
        let x_spur = quantifier.bound_vars[0].0;
        let mut subst: FxHashMap<Spur, TermId> = FxHashMap::default();
        subst.insert(x_spur, seven);

        let result = integration
            .apply_substitution(&quantifier, &subst, &mut manager)
            .expect("substitution of x:=7 must fully ground the Distinct body");

        let free = collect_free_vars(result, &manager);
        assert!(
            !free.contains(&x),
            "Distinct body still contains free bound variable x after substitution"
        );
    }

    /// Finding #2: a nested quantifier that re-binds the same variable name
    /// must be left intact by capture-avoiding substitution and must NOT be
    /// mis-flagged as a leftover free variable.
    #[test]
    fn test_audit_substitution_respects_inner_shadowing() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let bool_sort = manager.sorts.bool_sort;

        // Inner: (exists ((x Int)) (>= x 0)) -- rebinds x.
        let x_inner = manager.mk_var("x", int_sort);
        let zero = manager.mk_int(BigInt::from(0));
        let inner_body = manager.mk_ge(x_inner, zero);
        let inner = manager.mk_exists([("x", int_sort)], inner_body);

        // Outer body: (and P inner) where P mentions the outer x.
        let x_outer = manager.mk_var("x", int_sort);
        let p = manager.mk_gt(x_outer, zero);
        let outer_body = manager.mk_and(vec![p, inner]);
        let forall = manager.mk_forall([("x", int_sort)], outer_body);

        let mut integration = MBQIIntegration::new();
        integration.add_quantifier(forall, &manager);
        let quantifier = integration.quantifiers[0].clone();

        let five = manager.mk_int(BigInt::from(5));
        let x_spur = quantifier.bound_vars[0].0;
        let mut subst: FxHashMap<Spur, TermId> = FxHashMap::default();
        subst.insert(x_spur, five);

        // Should succeed: the inner exists legitimately keeps its own x; only
        // the outer occurrence is replaced.
        let result = integration.apply_substitution(&quantifier, &subst, &mut manager);
        assert!(
            result.is_some(),
            "capture-avoiding substitution with inner shadowing must not be \
             rejected as a leftover-bound-variable internal error"
        );

        // Sanity: the bool sort remains distinct from the int sort (guards
        // against accidental sort collapse in this fixture).
        assert_ne!(int_sort, bool_sort);
    }

    /// Finding (solver-p3b #3): a universal quantifier whose body simplifies to
    /// `true` regardless of its bound variable (e.g. `forall x. f(x) = f(x)`)
    /// must be reported `Satisfied` even over the infinite Int domain, so simple
    /// UFLIA tautological quantifiers return sat rather than Unknown.
    #[test]
    fn test_audit_trivially_valid_quantifier_is_satisfied() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let f_x = manager.mk_apply("f", [x], int_sort);
        let body = manager.mk_eq(f_x, f_x); // f(x) = f(x)  ≡ true
        let forall = manager.mk_forall([("x", int_sort)], body);

        let mut integration = MBQIIntegration::new();
        integration.add_quantifier(forall, &manager);

        let model = FxHashMap::default();
        let result = integration.check_with_model(&model, &mut manager);
        assert!(
            result.is_sat(),
            "forall x:Int. f(x) = f(x) is a tautology and must be Satisfied, \
             got {result:?}"
        );
    }

    /// Guard: the trivially-valid recognition must NOT grant sat for a
    /// non-tautological body.  `forall x. x >= -10` does not simplify to true
    /// and is in fact false at x = -11, so it must not be reported sat.
    #[test]
    fn test_audit_trivially_valid_does_not_overreach() {
        use num_bigint::BigInt;
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let neg_ten = manager.mk_int(BigInt::from(-10));
        let body = manager.mk_ge(x, neg_ten);
        let forall = manager.mk_forall([("x", int_sort)], body);

        let mut integration = MBQIIntegration::new();
        integration.add_quantifier(forall, &manager);

        let model = FxHashMap::default();
        let result = integration.check_with_model(&model, &mut manager);
        assert!(
            !result.is_sat(),
            "forall x:Int. x >= -10 is not a tautology and must not be granted \
             sat by trivial-validity recognition, got {result:?}"
        );
    }
}
