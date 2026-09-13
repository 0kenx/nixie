//! Z3-style model-based quantifier checking with a nested solver.
//!
//! # What this module does
//!
//! For each *universal* quantifier `q = forall x1..xn. body`, this engine
//! decides `q` against the **completed** candidate model in one shot, the way
//! Z3's `smt_model_checker` (its MBQI core) does:
//!
//! 1. **Complete the model.**  Every uninterpreted function is made total by
//!    choosing an `else` value (its explicit `else_value` when the completion
//!    pass set one, else the most frequent entry result, else the sort
//!    default).  Choosing an `else` is a legitimate interpretation decision,
//!    not a fabricated fact: the completed model *is* "entries plus else", and
//!    step 3 verifies every claim against exactly that interpretation.
//!
//! 2. **Evaluate the body under the completed model**, keeping the bound
//!    variables symbolic.  Ground subterms collapse to their model values; an
//!    application whose arguments are all concrete resolves to its entry
//!    result or the `else`; an application with a symbolic argument becomes
//!    the entry table written out as an `ite` chain (Z3's "macro" expansion of
//!    a `func_interp`) whose final leaf is the `else`.  The result `body'` is
//!    a formula over the bound variables, value literals and the theories'
//!    operators only — no uninterpreted function reaches the solver free.
//!
//! 3. **Skolemize and refute.**  Assert `not body'[sk1..skn]` (fresh Skolem
//!    constants for the bound variables) into a fresh, budgeted, nested
//!    [`Solver`] and run a complete CDCL(T) check:
//!    * `unsat` — no way to falsify the body under the completed
//!      interpretation, so the completed model satisfies `q`.  Because the
//!      completed model is a *total* interpretation that extends the ground
//!      model (entries are exactly the ground solver's pinned values), `q`
//!      being satisfied makes the whole assertion set satisfiable in the
//!      ordinary semantic sense.
//!    * `sat` — the nested model's values for the Skolem constants are
//!      falsifying terms; the caller instantiates `q` with them.  The lemma
//!      `body[x := t]` is a logical consequence of `q` for *any* ground `t`,
//!      so a "spurious" counterexample (one the nested solver found using an
//!      `else` choice that later rounds revise) is always sound: the outer
//!      solver re-checks the lemma against the real constraints.
//!    * `unknown` / budget exhausted — decline; the caller keeps its existing
//!      counterexample-search path.  Declining can only cost completeness.
//!
//! # Soundness of the `else` choice
//!
//! The completed model's domain for an *uninterpreted* sort is the model's
//! finite universe, and the Skolem constants of such sorts are restricted to
//! that universe (Z3's `restrict_to_universe`), matching the finite-model
//! semantics of uninterpreted sorts.  For interpreted sorts (`Real`, `Int`,
//! `Bool`, ...) the `ite` chain covers the whole domain: each point either
//! hits an entry (the chain says so) or falls through to the `else`.  So
//! evaluating `not body'[sk]` decides the quantifier over the *entire* domain
//! of every bound variable, not a sample — that is what makes an `unsat`
//! verdict a genuine satisfaction proof rather than "no counterexample was
//! found among the candidates".
//!
//! # Why a nested full solver instead of a term evaluator
//!
//! The bodies that matter are not decidable by term-level evaluation:
//! `f3(f4, f6 + v) = -f3(f4, v)` needs the arithmetic of `f6 + v` to be
//! *solved with*, not just folded; `member(x, s1) /\ subset(s1, s2) =>
//! member(x, s2)` is vacuously true for every `x` outside the finitely many
//! entry arguments, which a point sample can never establish over an
//! infinite `Real` domain.  A CDCL(T) check of the negated, completed body
//! decides both in one call.  Z3 pays exactly this cost per quantifier per
//! MBQI round (`model_checker::check`); we bound it with conflict budgets
//! and a nesting-depth guard (the nested solver's own quantifier loop runs
//! the legacy engines only — never a second nested check).
//!
//! Reference: `src/smt/smt_model_checker.cpp` in Z3 (`assert_neg_q_m`,
//! `model_checker::check`, `add_instance`), and the model evaluator's
//! completion (`src/model/model_evaluator.cpp`, `model_completion = true`).

use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::interner::Spur;
use nixie_core::sort::{SortId, SortKind};
use num_bigint::BigInt;
use num_rational::Rational64;
use num_traits::{One, ToPrimitive, Zero};
use smallvec::SmallVec;

use super::QuantifiedFormula;
use super::model_completion::{CompletedModel, FunctionEntry, FunctionInterpretation};

#[allow(unused_imports)]
use crate::prelude::*;
use crate::resource_limits::ResourceLimits;
use crate::{Solver, SolverResult};

type ChildList = SmallVec<[TermId; 4]>;

/// Per-check conflict budget for the nested solve.
///
/// Counterexample goals after completion are small (value literals plus ite
/// chains); this cap exists so a pathological goal cannot dominate the outer
/// search.  Hitting it declines, which costs completeness only.
const AUX_CONFLICT_LIMIT: u64 = 4_096;

/// Per-check decision budget for the nested solve.
const AUX_DECISION_LIMIT: u64 = 65_536;

/// Total nested-conflict budget for one `ModelChecker` lifetime (one outer
/// solve).  After it is spent the checker declines every further request.
const TOTAL_CONFLICT_BUDGET: u64 = 50_000;

/// Total number of nested checks one `ModelChecker` will perform.
const TOTAL_CHECK_BUDGET: usize = 512;

/// Maximum number of entries per function written out as an `ite` chain.
///
/// Truncating a chain would misrepresent the completed model (an entry
/// argument would silently evaluate to the `else`), so an over-budget
/// function *declines the quantifier* instead — never a partial chain.
const MAX_ENTRIES_PER_FUNC: usize = 1024;

/// Maximum universe size for the finite-sort Skolem restriction clause.
const MAX_UNIVERSE_FOR_RESTRICTION: usize = 32;

/// Maximum size (in visited nodes) of one evaluation before declining.
const MAX_EVALUATED_BODY_SIZE: usize = 20_000;

/// Lifetime bound on `check_veto` second opinions (see there).
const MAX_VETO_CHECKS: usize = 32;

/// Hard cap on nested checks per quantifier across the whole `ModelChecker`
/// lifetime: a forced rerun's model *moves* (learned clauses change the
/// search) on every rerun, re-arming the same-model gate, so only a
/// lifetime cap bounds what a re-checked goal can spend.  Two gives a
/// converging quantifier one early check (round 0's model is usually
/// partial) and one against the settled model.
const MAX_CHECKS_PER_QUANTIFIER: u32 = 2;

/// Nesting depth guard: the nested solver's own quantifier loop must never
/// recurse without bound.  Depth 2 allows exactly one level of re-entry —
/// the aux goal of a `forall`-`exists` body (e.g. the set-theory axiom
/// `~subset(s1,s2) => exists x. ...` negates to a nested `forall` that the
/// aux solver's own MBQI must decide) — while a deeper nest still declines.
/// Every level keeps its own conflict/check budgets, so the added depth is
/// work-bounded, not unbounded recursion.
static NESTED_DEPTH: core::sync::atomic::AtomicU32 = core::sync::atomic::AtomicU32::new(0);

/// RAII guard incrementing [`NESTED_DEPTH`] for the nested solve so a
/// too-deep re-entering check (from inside the nested solver's MBQI loop)
/// sees the depth and declines.
struct NestingGuard;

impl NestingGuard {
    fn enter() -> Option<Self> {
        let depth = NESTED_DEPTH.load(Ordering::Acquire);
        if depth >= 2 {
            return None;
        }
        NESTED_DEPTH.store(depth + 1, Ordering::Release);
        Some(Self)
    }
}

impl Drop for NestingGuard {
    fn drop(&mut self) {
        let depth = NESTED_DEPTH.load(Ordering::Acquire);
        NESTED_DEPTH.store(depth.saturating_sub(1), Ordering::Release);
    }
}

use core::sync::atomic::Ordering;

/// The outcome of checking one universal quantifier against the completed
/// model.
#[derive(Debug)]
pub(crate) enum ModelCheckOutcome {
    /// The completed model provably satisfies the quantifier: the negated,
    /// completed, Skolemized body is unsatisfiable in a full nested check.
    Satisfied,
    /// The falsifying assignments found by the nested check; the maps carry
    /// bound-variable names to ground falsifying terms (Z3 enumerates several
    /// per round with blocking clauses — see `add_blocking_clause` — so one
    /// round exhausts the current model's falsifier set instead of re-finding
    /// the same already-instantiated pair until the round budget dies).  The
    /// caller builds the (always sound) instantiation lemmas from them.
    Counterexample {
        /// Bound-variable name -> ground falsifying term, one map per falsifier.
        substitutions: Vec<FxHashMap<Spur, TermId>>,
    },
    /// The checker could not run (budget, unsupported construct, nesting):
    /// the caller falls back to its existing counterexample search.
    Declined,
}

/// Budgeted Z3-style model checker (see the module docs).
#[derive(Debug)]
pub(crate) struct ModelChecker {
    /// Monotone fresh-Skolem counter; names are `mbqi!sk<N>`.
    skolem_counter: u64,
    /// Nested checks performed so far.
    checks_performed: usize,
    /// Conflict budgets consumed by nested checks so far.
    conflicts_spent: u64,
    /// Size of the completed model's assignment table when this quantifier
    /// was last checked.  A check against a *changed* model is always in
    /// budget (the model moved, so the previous verdicts say nothing); a
    /// re-check against the *same* model re-pays a nested solve for an
    /// outcome that is already known, and those are what the signature gate
    /// below refuses — the re-checked-goal (verdict-cache bypass) and
    /// thrashing-round cases.
    last_model_signature: FxHashMap<TermId, u64>,
    /// Total nested checks spent per quantifier (hard lifetime cap).
    checks_of: FxHashMap<TermId, u32>,
    /// Model signatures at which the nested refutation *found a falsifier*
    /// for a quantifier (the aux `sat` verdict, with the Skolems confined
    /// to the finite universe).  A legacy "satisfied on the whole universe"
    /// claim for the same quantifier under the same model is then
    /// demonstrably wrong — the falsifier lives at a domain point the tuple
    /// check missed or mis-evaluated — and `is_vetoed` lets the caller
    /// refuse the verdict.  The memory is per-signature, so a genuinely
    /// moved model re-earns its certification.
    falsified_at: FxHashMap<TermId, Vec<u64>>,
    /// Second opinions spent (see [`ModelChecker::check_veto`]).
    veto_checks: usize,
    /// Last decline reason, for stats/debugging.
    pub(crate) last_decline: Option<&'static str>,
}

impl Default for ModelChecker {
    fn default() -> Self {
        Self::new()
    }
}

impl ModelChecker {
    pub(crate) fn new() -> Self {
        Self {
            skolem_counter: 0,
            checks_performed: 0,
            conflicts_spent: 0,
            last_model_signature: FxHashMap::default(),
            checks_of: FxHashMap::default(),
            falsified_at: FxHashMap::default(),
            veto_checks: 0,
            last_decline: None,
        }
    }

    /// Record that the check of `quantifier` was productive (its mined
    /// counterexample became a fresh instantiation): the fruitless streak
    /// resets and the model signature is forgotten, so a later round may
    /// ask again (the fresh lemma perturbs the ground model, so the next
    /// completed model will differ anyway — the signature reset is
    /// belt-and-braces for the case where it does not).
    /// Record that `quantifier` was falsified under the current model (the
    /// aux-`sat` verdict).  See [`ModelChecker::falsified_at`].
    pub(crate) fn mark_falsified(&mut self, quantifier: TermId, signature: u64) {
        self.falsified_at
            .entry(quantifier)
            .or_default()
            .push(signature);
    }

    /// Soundness gate for the legacy finite-exhaustion `Satisfied`: has the
    /// completed model *demonstrably failed* this quantifier at a domain
    /// point (an aux-`sat` verdict with the Skolems confined to the finite
    /// universe)?
    ///
    /// This bypasses the cost caps by design: it runs only in the rare
    /// moment the sampling engines are about to certify the whole goal from
    /// their own tuple evaluations — an evaluation with a documented liar
    /// in its lookup path (stale-entry TermId matches, the Rodin
    /// false-`sat`) — so this is the second opinion that either clears the
    /// verdict (`false`) or vetoes it (`true`, including on an
    /// undetermined check: a wrong `unknown` costs completeness, an
    /// unvetted liar costs soundness).  Results are memoized per
    /// (quantifier, model signature).
    pub(crate) fn check_veto(
        &mut self,
        q: &QuantifiedFormula,
        model: &CompletedModel,
        logic: Option<&str>,
        manager: &mut TermManager,
    ) -> bool {
        if !q.is_universal || q.bound_vars.is_empty() {
            return false;
        }
        let signature = completed_model_signature(model);
        if self.is_vetoed(q.term, signature) {
            return true;
        }
        // Lifetime bound on second opinions: a forced rerun moves the model
        // (fresh signatures) on every rerun, so an unbounded veto budget
        // would be re-paid hundreds of times.  Once spent, the veto is
        // answered conservatively (`true` — refuse the legacy verdict),
        // which costs completeness only.
        if self.veto_checks >= MAX_VETO_CHECKS {
            return true;
        }
        self.veto_checks += 1;
        let Some(_guard) = NestingGuard::enter() else {
            // Cannot run a second opinion here: stay conservative.
            return true;
        };
        // The completed model's entry tables must be chain-able for the
        // evaluation; over-budget tables leave the check undetermined.
        for interp in model.function_interps.values() {
            if interp.entries.len() > MAX_ENTRIES_PER_FUNC {
                return true;
            }
        }
        let mut bound_names: FxHashSet<Spur> = FxHashSet::default();
        for &(name, _) in &q.bound_vars {
            bound_names.insert(name);
        }
        if collect_nested_binder_names(q.body, manager, &mut bound_names).is_err() {
            return true;
        }
        let else_table = choose_else_table(model, manager);
        let body_completed =
            match CompletionEval::run(q.body, model, &bound_names, &else_table, manager) {
                Ok(body) => body,
                Err(_) => return true,
            };
        let mut skolem_terms: Vec<(Spur, SortId, TermId)> = Vec::new();
        for &(name, sort) in &q.bound_vars {
            let sk_name = format!("mbqi!veto{}", self.skolem_counter);
            self.skolem_counter = self.skolem_counter.wrapping_add(1);
            let sk = manager.mk_var(&sk_name, sort);
            skolem_terms.push((name, sort, sk));
        }
        match self.aux_refute(body_completed, &skolem_terms, model, logic, manager) {
            Ok(SolverResult::Unsat) => false,
            Ok(_) => {
                // Parity with the escalation's else-search: the closed-world
                // completion (Bool-valued else forced false) is an equally
                // legitimate total interpretation, and a goal certified
                // under it is genuinely satisfied — clear the veto.
                let closed_else = closed_world_else_table(model, manager);
                if let Ok(body_closed) =
                    CompletionEval::run(q.body, model, &bound_names, &closed_else, manager)
                    && body_closed != body_completed
                    && matches!(
                        self.aux_refute(body_closed, &skolem_terms, model, logic, manager),
                        Ok(SolverResult::Unsat)
                    )
                {
                    return false;
                }
                self.mark_falsified(q.term, signature);
                true
            }
            Err(_) => true,
        }
    }

    /// The signature of a completed model (see [`completed_model_signature`]).
    pub(crate) fn signature_of(&self, model: &CompletedModel) -> u64 {
        completed_model_signature(model)
    }

    /// Whether `quantifier` was falsified under this exact model.
    pub(crate) fn is_vetoed(&self, quantifier: TermId, signature: u64) -> bool {
        self.falsified_at
            .get(&quantifier)
            .is_some_and(|sigs| sigs.contains(&signature))
    }

    pub(crate) fn mark_productive(&mut self, quantifier: TermId) {
        self.last_model_signature.remove(&quantifier);
    }

    /// Check the universal quantifier `q` against the completed `model`.
    pub(crate) fn check(
        &mut self,
        q: &QuantifiedFormula,
        model: &CompletedModel,
        logic: Option<&str>,
        manager: &mut TermManager,
    ) -> ModelCheckOutcome {
        if !q.is_universal {
            self.last_decline = Some("not universal");
            return ModelCheckOutcome::Declined;
        }
        if q.bound_vars.is_empty() {
            self.last_decline = Some("no bound variables");
            return ModelCheckOutcome::Declined;
        }
        if self.checks_performed >= TOTAL_CHECK_BUDGET {
            self.last_decline = Some("check budget exhausted");
            return ModelCheckOutcome::Declined;
        }
        if self.conflicts_spent >= TOTAL_CONFLICT_BUDGET {
            self.last_decline = Some("conflict budget exhausted");
            return ModelCheckOutcome::Declined;
        }
        // Hard lifetime cap per quantifier: the global budgets bound the
        // total, but a forced rerun's model can *move* (learned clauses
        // change the search) on every one of its hundreds of reruns, each
        // move re-arming the same-model gate.  After this many nested
        // checks the quantifier has had its chance; the landed value.
        if self.checks_of.get(&q.term).copied().unwrap_or(0) >= MAX_CHECKS_PER_QUANTIFIER {
            self.last_decline = Some("per-quantifier check budget exhausted");
            return ModelCheckOutcome::Declined;
        }
        *self.checks_of.entry(q.term).or_insert(0) += 1;

        let signature = completed_model_signature(model);
        if self.last_model_signature.get(&q.term).copied() == Some(signature) {
            self.last_decline = Some("completed model unchanged since last check");
            return ModelCheckOutcome::Declined;
        }
        self.last_model_signature.insert(q.term, signature);
        let Some(_guard) = NestingGuard::enter() else {
            self.last_decline = Some("nested model check");
            return ModelCheckOutcome::Declined;
        };

        // Bound names: the outer quantifier's variables plus every nested
        // quantifier's variables (they stay symbolic inside their own body).
        let mut bound_names: FxHashSet<Spur> = FxHashSet::default();
        for &(name, _) in &q.bound_vars {
            bound_names.insert(name);
        }
        if let Err(reason) = collect_nested_binder_names(q.body, manager, &mut bound_names) {
            self.last_decline = Some(reason);
            return ModelCheckOutcome::Declined;
        }

        // Total interpretation: an else value for every function we may
        // need.  The entry cap counts *chain-relevant* entries — those
        // whose result differs from the function's else — because the
        // ite-chain construction (see `fold_apply`) skips the rest: the
        // enumerative seeder's thousands of default-valued pins must not
        // bury the structural ones.
        let else_preview = choose_else_table(model, manager);
        for interp in model.function_interps.values() {
            let Some(&else_val) = else_preview.get(&interp.name) else {
                continue;
            };
            let relevant = interp
                .entries
                .iter()
                .filter(|e| value_equal(e.result, else_val, manager) != Some(true))
                .count();
            if relevant > MAX_ENTRIES_PER_FUNC {
                if std::env::var_os("NIXIE_DEBUG_MC").is_some() {
                    eprintln!(
                        "[mc] declined: fn {} has {relevant} relevant entries ({} total)",
                        interp.name.into_inner().get(),
                        interp.entries.len()
                    );
                }
                self.last_decline = Some("function entry table too large");
                return ModelCheckOutcome::Declined;
            }
        }

        // Evaluate the body under the completed interpretation.
        let body_completed = match CompletionEval::run(
            q.body,
            model,
            &bound_names,
            &choose_else_table(model, manager),
            manager,
        ) {
            Ok(body) => body,
            Err(reason) => {
                if std::env::var_os("NIXIE_DEBUG_MC").is_some() {
                    eprintln!("[mc] declined: {reason}");
                }
                self.last_decline = Some(reason);
                return ModelCheckOutcome::Declined;
            }
        };
        if std::env::var_os("NIXIE_DEBUG_MC").is_some() {
            eprintln!(
                "[mc] check q={:?}: model.macros = {}",
                q.term,
                model.macros.len()
            );
            let printer = nixie_core::smtlib::Printer::new(manager);
            eprintln!("[mc] orig  = {}", printer.print_term(q.body));
            eprintln!("[mc] body' = {}", printer.print_term(body_completed));
            for (f, interp) in &model.function_interps {
                eprintln!(
                    "[mc]   fn {}: {} entries, else={:?}",
                    f.into_inner().get(),
                    interp.entries.len(),
                    interp.else_value
                );
            }
        }

        // Skolemize the bound variables.
        let mut skolem_terms: Vec<(Spur, SortId, TermId)> = Vec::new();
        for &(name, sort) in &q.bound_vars {
            let sk_name = format!("mbqi!sk{}", self.skolem_counter);
            self.skolem_counter = self.skolem_counter.wrapping_add(1);
            let sk = manager.mk_var(&sk_name, sort);
            skolem_terms.push((name, sort, sk));
        }
        let _ = &skolem_terms;

        // Refute the completed interpretation (primary else choice).
        let result = self.aux_refute(body_completed, &skolem_terms, model, logic, manager);
        // Else-search (Z3 `smt_model_finder`'s default search, bounded to
        // one candidate): when the primary completion admits a falsifier,
        // retry with every *Bool-valued* function's else forced to `false`
        // — the closed-world completion under which membership-style axioms
        // are vacuously satisfied off their entry tables.  Both are total
        // extensions of the same entries, so an `unsat` under either is a
        // sound satisfaction proof; the search only affects which
        // completions we can certify.
        let result = if result.as_ref().is_ok_and(|r| *r == SolverResult::Sat) {
            let closed_else = closed_world_else_table(model, manager);
            let body_closed =
                CompletionEval::run(q.body, model, &bound_names, &closed_else, manager)
                    .ok()
                    .filter(|body| *body != body_completed);
            if let Some(body_closed) = body_closed {
                let retry = self.aux_refute(body_closed, &skolem_terms, model, logic, manager);
                if retry.as_ref().is_ok_and(|r| *r == SolverResult::Unsat) {
                    if std::env::var_os("NIXIE_DEBUG_MC").is_some() {
                        eprintln!("[mc] aux verdict (closed-world else): satisfied");
                    }
                    self.last_decline = None;
                    return ModelCheckOutcome::Satisfied;
                }
            }
            result
        } else {
            result
        };
        if std::env::var_os("NIXIE_DEBUG_MC").is_some() {
            eprintln!("[mc] aux verdict q={:?}: {:?}", q.term, result);
        }

        match result {
            Ok(SolverResult::Unsat) => {
                self.last_decline = None;
                ModelCheckOutcome::Satisfied
            }
            Ok(SolverResult::Sat) => {
                // A falsifier exists (the unrestricted nested check proved
                // it).  Mine *relevant* ones term-level, Z3-style
                // (`restrict_sks_to_inst_set` + `value2expr`): enumerate
                // combinations of the instantiation set — the values the
                // current model already distinguishes (entry arguments and
                // results, assigned values) — evaluate the completed body
                // under each with this module's own evaluator, and keep the
                // combinations that evaluate to `false` (up to a small cap,
                // the multi-cex role of Z3's `add_blocking_clause`).  The
                // unrestricted falsifier itself is an arbitrary point whose
                // lemmas never interlock, and the nested model does not
                // report values for theory-irrelevant Skolems, so it is not
                // a usable binding source; term-level mining needs neither.
                let else_table = choose_else_table(model, manager);
                let (inst_sets, value_to_term) =
                    self.build_instantiation_set(&skolem_terms, &bound_names, model, manager);
                let mut skolem_map: FxHashMap<TermId, TermId> = FxHashMap::default();
                for &(name, sort, sk) in &skolem_terms {
                    let name_str = manager.resolve_str(name).to_string();
                    skolem_map.insert(manager.mk_var(&name_str, sort), sk);
                }

                /// How many distinct falsifiers one round mines.
                const MAX_CEX_PER_CHECK: usize = 6;
                /// Bound on the combination product tried per check.
                const MAX_COMBO_PRODUCT: usize = 256;

                // The combo domain per bound variable: for an *uninterpreted*
                // sort the finite universe itself — the restriction clause
                // confines the Skolem to it, so the aux falsifier lives
                // there, and inst-set-only mining misses points the seeding
                // never referenced (a `seteq(z,z) = (z=z)` axiom fails at
                // every universe element whose reflexive pin is missing,
                // however `z` was constructed).  Interpreted sorts keep the
                // instantiation set (their "universe" is an infinite-domain
                // sample, not a domain).
                let sets: Vec<Vec<TermId>> = skolem_terms
                    .iter()
                    .map(|&(_, sort, _)| {
                        let finite_universe = manager
                            .sorts
                            .get(sort)
                            .is_some_and(|s| matches!(s.kind, SortKind::Uninterpreted(_)))
                            .then(|| model.universe(sort))
                            .flatten()
                            .filter(|u| !u.is_empty() && u.len() <= MAX_UNIVERSE_FOR_RESTRICTION)
                            .map(|u| u.to_vec());
                        finite_universe
                            .unwrap_or_else(|| inst_sets.get(&sort).cloned().unwrap_or_default())
                    })
                    .collect();
                if sets.iter().any(|s| s.is_empty()) {
                    // Some bound variable has no candidate values at all:
                    // nothing sensible to instantiate with.
                    self.last_decline = Some("empty instantiation set");
                    return ModelCheckOutcome::Declined;
                }

                let false_term = manager.mk_false();
                let mut mined: Vec<FxHashMap<Spur, TermId>> = Vec::new();
                let mut odometer = vec![0usize; sets.len()];
                let mut tried = 0usize;
                'combo: loop {
                    if tried >= MAX_COMBO_PRODUCT || mined.len() >= MAX_CEX_PER_CHECK {
                        break;
                    }
                    tried += 1;
                    // Evaluate the completed body under this combination.
                    let mut subst: FxHashMap<TermId, TermId> = FxHashMap::default();
                    for (i, &(name, sort, _)) in skolem_terms.iter().enumerate() {
                        let value = sets[i][odometer[i]];
                        let name_str = manager.resolve_str(name).to_string();
                        subst.insert(manager.mk_var(&name_str, sort), value);
                    }
                    let substituted = manager.substitute(body_completed, &subst);
                    let empty_bound: FxHashSet<Spur> = FxHashSet::default();
                    let evaluated =
                        CompletionEval::run(substituted, model, &empty_bound, &else_table, manager);
                    if evaluated.is_ok_and(|t| t == false_term) {
                        let mut falsifying: FxHashMap<Spur, TermId> = FxHashMap::default();
                        for (i, &(name, _, _)) in skolem_terms.iter().enumerate() {
                            let raw = sets[i][odometer[i]];
                            let chosen = value_to_term.get(&raw).copied().unwrap_or(raw);
                            falsifying.insert(name, chosen);
                        }
                        mined.push(falsifying);
                    }
                    // Advance the odometer (variable 0 fastest).
                    for i in 0..odometer.len() {
                        odometer[i] += 1;
                        if odometer[i] < sets[i].len() {
                            break;
                        }
                        odometer[i] = 0;
                        if i + 1 == odometer.len() {
                            break 'combo;
                        }
                    }
                }

                if mined.is_empty() {
                    // No instantiation-set combination falsifies, but the
                    // unrestricted Skolem (confined to the finite universe by
                    // the restriction clause) DID: the completed model fails
                    // this quantifier at a domain point the sampling tuple
                    // check never saw or mis-evaluated.  There is no useful
                    // lemma to mine, so report the empty counterexample —
                    // the caller treats an aux-`sat` verdict as a veto on
                    // any legacy "satisfied on the whole universe" claim
                    // (the Rodin false-`sat` shape).
                    self.last_decline = Some("no relevant falsifier");
                    return ModelCheckOutcome::Counterexample {
                        substitutions: Vec::new(),
                    };
                }
                self.last_decline = None;
                if std::env::var_os("NIXIE_DEBUG_MC").is_some() {
                    let printer = nixie_core::smtlib::Printer::new(manager);
                    for falsifying in &mined {
                        let subs: Vec<String> = falsifying
                            .iter()
                            .map(|(k, v)| {
                                format!("{} := {}", manager.resolve_str(*k), printer.print_term(*v))
                            })
                            .collect();
                        eprintln!("[mc] cex bindings: {}", subs.join(", "));
                    }
                }
                ModelCheckOutcome::Counterexample {
                    substitutions: mined,
                }
            }
            Ok(SolverResult::Unknown) | Err(_) => {
                self.last_decline = Some("nested check undetermined");
                ModelCheckOutcome::Declined
            }
        }
    }

    /// Build the nested refutation goal for `body` (a completed-model
    /// evaluation with the Skolem substitution applied) and check it:
    /// `unsat` means the completed model satisfies the quantifier.
    ///
    /// Budgets: one nested solve per call (conflicts/decisions capped;
    /// `checks_performed`/`conflicts_spent` advance so the global caps
    /// bound the total).
    fn aux_refute(
        &mut self,
        body: TermId,
        skolem_terms: &[(Spur, SortId, TermId)],
        model: &CompletedModel,
        logic: Option<&str>,
        manager: &mut TermManager,
    ) -> core::result::Result<SolverResult, crate::resource_limits::ResourceExhausted> {
        let mut aux = Solver::new();
        aux.set_logic(logic.unwrap_or("ALL"));
        // Restrict finite-domain Skolems to the model's universe (Z3's
        // `restrict_to_universe` under `is_finite`).  ONLY uninterpreted
        // sorts qualify: their completed model *is* the finite universe
        // (finite-model semantics), so the restriction loses no points.
        // An interpreted sort's universe entry is merely a *sample* of the
        // model's values — restricting an Int/Real Skolem to it would
        // fabricate an unsat verdict out of values the skolem was never
        // allowed to take (the false-`Satisfied` on `2v+1 = y` with the
        // falsifier outside the sample).
        for &(_name, sort, sk) in skolem_terms {
            let finite_universe = manager
                .sorts
                .get(sort)
                .is_some_and(|s| matches!(s.kind, SortKind::Uninterpreted(_)))
                .then(|| model.universe(sort))
                .flatten();
            if let Some(universe) = finite_universe
                && !universe.is_empty()
                && universe.len() <= MAX_UNIVERSE_FOR_RESTRICTION
            {
                let restriction: Vec<TermId> =
                    universe.iter().map(|&u| manager.mk_eq(sk, u)).collect();
                aux.assert(manager.mk_or(restriction), manager);
            }
        }

        // not body[sk]  — refute the completed interpretation.
        let substitution = skolem_var_map(skolem_terms, manager);
        let skolemized = manager.substitute(body, &substitution);
        let goal = manager.mk_not(skolemized);
        aux.assert(goal, manager);

        self.checks_performed += 1;
        let limits = ResourceLimits::new()
            .with_max_conflicts(AUX_CONFLICT_LIMIT)
            .with_max_decisions(AUX_DECISION_LIMIT);
        let verdict = aux.check_with_limits(manager, &limits);
        self.conflicts_spent = self.conflicts_spent.saturating_add(AUX_CONFLICT_LIMIT);
        verdict
    }

    /// Build the per-sort *instantiation sets* and the value→term map for
    /// translating bindings back into problem terms (Z3's
    /// `restrict_sks_to_inst_set` / `value2expr`).
    ///
    /// The set holds the values the current model already distinguishes:
    /// every function entry's (normalized) arguments of this sort and its
    /// results, plus the values of the model's assignments of this sort.
    /// The map prefers, for each value, the entry-argument term it is the
    /// value of, then a compound assigned term, then any assigned term —
    /// falling back to the value itself.
    fn build_instantiation_set(
        &mut self,
        skolem_terms: &[(Spur, SortId, TermId)],
        bound_names: &FxHashSet<Spur>,
        model: &CompletedModel,
        manager: &mut TermManager,
    ) -> (FxHashMap<SortId, Vec<TermId>>, FxHashMap<TermId, TermId>) {
        /// Cap on the size of one sort's instantiation set.
        const MAX_INST_SET: usize = 16;
        let _ = skolem_terms;

        // The model's assignment table and entry arguments can contain
        // *encoding artifacts* — terms whose free variables are named like
        // quantifier bound variables (the encoder internalized the body
        // with its binders as constants).  Such a term is not a ground
        // domain element; instantiating with it emits a lemma about a
        // stray global constant (the `?s1 := ?s2` junk bindings).
        let mentions_bound = |term: TermId| -> bool {
            nixie_core::ast::traversal::collect_free_vars_including_patterns(term, manager)
                .iter()
                .any(|&v| {
                    manager.get(v).is_some_and(
                        |n| matches!(n.kind, TermKind::Var(name) if bound_names.contains(&name)),
                    )
                })
        };

        let mut sorts: FxHashMap<SortId, (Vec<TermId>, FxHashMap<TermId, TermId>)> =
            FxHashMap::default();
        let value_of =
            |sort: SortId,
             value: TermId,
             term: TermId,
             table: &mut FxHashMap<SortId, (Vec<TermId>, FxHashMap<TermId, TermId>)>| {
                let entry = table
                    .entry(sort)
                    .or_insert_with(|| (Vec::new(), FxHashMap::default()));
                if !entry.0.contains(&value) && entry.0.len() < MAX_INST_SET {
                    entry.0.push(value);
                }
                // First entry-arg term for a value wins; compound terms beat
                // constants beat literals by insertion order below.
                entry.1.entry(value).or_insert(term);
            };

        // Entry arguments (normalized to values) and results.  Skip
        // artifacts that mention bound-variable names (see
        // `mentions_bound`).
        for interp in model.function_interps.values() {
            for entry in &interp.entries {
                for (i, &arg) in entry.args.iter().enumerate() {
                    let Some(&domain_sort) = interp.domain.get(i) else {
                        continue;
                    };
                    if mentions_bound(arg) {
                        continue;
                    }
                    let norm = model.assignments.get(&arg).copied().unwrap_or(arg);
                    value_of(domain_sort, norm, arg, &mut sorts);
                }
                if !mentions_bound(entry.result) {
                    value_of(interp.range, entry.result, entry.result, &mut sorts);
                }
            }
        }
        // Assigned terms of each sort (compound terms first, so they win
        // the map over bare constants).
        let mut assigned: Vec<(SortId, TermId, TermId)> = Vec::new();
        for (&term, &value) in &model.assignments {
            let Some(node) = manager.get(term) else {
                continue;
            };
            if mentions_bound(term) || mentions_bound(value) {
                continue;
            }
            assigned.push((node.sort, term, value));
        }
        assigned.sort_by_key(|(sort, term, value)| {
            let _ = value;
            let compound = manager.get(*term).is_some_and(|n| {
                !matches!(
                    n.kind,
                    TermKind::Var(_) | TermKind::IntConst(_) | TermKind::RealConst(_)
                )
            });
            (sort.0, !compound, term.0)
        });
        for (sort, term, value) in assigned {
            value_of(sort, value, term, &mut sorts);
        }

        let mut sets: FxHashMap<SortId, Vec<TermId>> = FxHashMap::default();
        let mut value_to_term: FxHashMap<TermId, TermId> = FxHashMap::default();
        for (sort, (values, map)) in sorts {
            for (value, term) in map {
                value_to_term.insert(value, term);
            }
            sets.insert(sort, values);
        }
        (sets, value_to_term)
    }
}

/// Build the `Var` term for each skolemized bound variable, for
/// [`TermManager::substitute`].  Hash-consing makes this the very same
/// `TermId` as the free occurrences in the evaluated body (the quantifier
/// machinery builds bound-variable occurrences the same way).
fn skolem_var_map(
    skolem_terms: &[(Spur, SortId, TermId)],
    manager: &mut TermManager,
) -> FxHashMap<TermId, TermId> {
    let mut map: FxHashMap<TermId, TermId> = FxHashMap::default();
    for &(name, sort, sk) in skolem_terms {
        let name_str = manager.resolve_str(name).to_string();
        let var = manager.mk_var(&name_str, sort);
        map.insert(var, sk);
    }
    map
}

/// The else table: a total-interpretation value for every function.
///
/// Soundness does not depend on these choices (any `else` defines a
/// legitimate total extension of the entry table, and the nested check
/// verifies against exactly these); the preference order only affects how
/// quickly the outer loop converges.
fn choose_else_table(model: &CompletedModel, manager: &mut TermManager) -> FxHashMap<Spur, TermId> {
    let mut table: FxHashMap<Spur, TermId> = FxHashMap::default();
    for (&func, interp) in &model.function_interps {
        if let Some(else_val) = choose_else(interp, model, manager) {
            table.insert(func, else_val);
        }
    }
    table
}

/// Whether the completed body still applies some *Bool-valued* function at
/// a position whose arguments mention a bound variable — the vacuity shape
/// the closed-world else-search exists for (`member(x, s)` with symbolic
/// `x`).  Cheap structural scan over the already-built body, so the retry
/// costs nothing on arithmetic goals.
fn body_uses_bool_fn_at_symbolic_position(
    body: TermId,
    model: &CompletedModel,
    manager: &TermManager,
) -> bool {
    let mut bool_fns: FxHashSet<Spur> = FxHashSet::default();
    for (&func, interp) in &model.function_interps {
        if interp.range == manager.sorts.bool_sort {
            bool_fns.insert(func);
        }
    }
    if bool_fns.is_empty() {
        return false;
    }
    // Walk with the bound-variable names unknown here; approximate by
    // treating every Var as symbolic (over-approximation only gates a
    // *retry*, never a verdict).
    let mut stack = vec![body];
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    while let Some(term) = stack.pop() {
        if !visited.insert(term) || visited.len() > 20_000 {
            return false;
        }
        let Some(node) = manager.get(term) else {
            continue;
        };
        if let TermKind::Apply { func, args } = &node.kind
            && bool_fns.contains(func)
            && args.iter().any(|&a| term_mentions_var(a, manager))
        {
            return true;
        }
        let mut children: SmallVec<[TermId; 4]> = SmallVec::new();
        push_children(&node.kind, &mut children);
        stack.extend(children.iter().copied());
    }
    false
}

/// Whether `term` contains any `Var` node (an over-approximation of
/// "mentions a bound variable" — see [`body_uses_bool_fn_at_symbolic_position`]).
fn term_mentions_var(term: TermId, manager: &TermManager) -> bool {
    let mut stack = vec![term];
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) || visited.len() > 20_000 {
            return false;
        }
        let Some(node) = manager.get(t) else {
            continue;
        };
        if matches!(node.kind, TermKind::Var(_)) {
            return true;
        }
        let mut children: SmallVec<[TermId; 4]> = SmallVec::new();
        push_children(&node.kind, &mut children);
        stack.extend(children.iter().copied());
    }
    false
}

/// A value-sensitive signature of the completed model: every (term, value)
/// pair and every function entry is hashed.  A length/count pair cannot see
/// a value *flip* (a lemma committing `member(sk,b) = true` over the same
/// term count reads as "unchanged"), so the veto and re-check gates keyed on
/// this must observe flips.
fn completed_model_signature(model: &CompletedModel) -> u64 {
    use core::hash::Hash;
    let mut hasher = rustc_hash::FxHasher::default();
    model.assignments.len().hash(&mut hasher);
    for (&k, &v) in &model.assignments {
        k.0.hash(&mut hasher);
        v.0.hash(&mut hasher);
    }
    model.function_interps.len().hash(&mut hasher);
    for interp in model.function_interps.values() {
        interp.entries.len().hash(&mut hasher);
        for entry in &interp.entries {
            for &a in &entry.args {
                a.0.hash(&mut hasher);
            }
            entry.result.0.hash(&mut hasher);
        }
    }
    core::hash::Hasher::finish(&hasher)
}

/// The closed-world else table: every *Bool-valued* function's else forced
/// to `false`, everything else as [`choose_else_table`] picks.  A candidate
/// completion for the else-search — legitimate (a total extension of the
/// same entries) and verified by the nested refutation before anything is
/// concluded from it.
fn closed_world_else_table(
    model: &CompletedModel,
    manager: &mut TermManager,
) -> FxHashMap<Spur, TermId> {
    let mut table = choose_else_table(model, manager);
    let false_term = manager.mk_false();
    for (&func, interp) in &model.function_interps {
        if interp.range == manager.sorts.bool_sort {
            table.insert(func, false_term);
        }
    }
    table
}

/// One function's else value:
///
/// 1. an `else_value` the completion pass already fixed;
/// 2. the most frequent entry result (first occurrence on ties) — Z3's
///    default when it builds a `func_interp` else;
/// 3. the model's sort default, or a structural fallback.
fn choose_else(
    interp: &FunctionInterpretation,
    model: &CompletedModel,
    manager: &mut TermManager,
) -> Option<TermId> {
    if let Some(else_val) = interp.else_value {
        return Some(else_val);
    }
    // Bool-valued functions take the closed-world default (`false`)
    // BEFORE the entry mode: once a lemma round pushes the true entries
    // past the false ones, the mode flips the else to `true`, every fresh
    // domain point then reads `member(x, s) = true`, the union/intersection
    // axioms fail at *every* new candidate, and the instantiation loop
    // diverges over the infinite index domain (the set9/16/19 stall).
    // `false`-unless-pinned is the standard finite-model reading (Z3's
    // `get_some_value(Bool)`); sound as a completion like any other.
    if interp.range == manager.sorts.bool_sort {
        let false_term = manager.mk_false();
        return Some(false_term);
    }
    if let Some((most_common, _)) = entry_result_mode(&interp.entries) {
        return Some(most_common);
    }
    sort_default(interp.range, model, manager)
}

/// The most frequent entry result (`(term, count)`), first occurrence
/// winning ties.
fn entry_result_mode(entries: &[FunctionEntry]) -> Option<(TermId, usize)> {
    let mut counts: FxHashMap<TermId, usize> = FxHashMap::default();
    let mut first: FxHashMap<TermId, usize> = FxHashMap::default();
    for (idx, entry) in entries.iter().enumerate() {
        *counts.entry(entry.result).or_insert(0) += 1;
        first.entry(entry.result).or_insert(idx);
    }
    counts
        .into_iter()
        .max_by_key(|(result, count)| (*count, core::cmp::Reverse(first[result])))
}

/// A default value for a sort: the model's own default, else a structural
/// zero/false of the sort.
///
/// This fabricates nothing about the *problem*: it is part of defining a
/// total interpretation, which the nested check then verifies.
fn sort_default(sort: SortId, model: &CompletedModel, manager: &mut TermManager) -> Option<TermId> {
    if let Some(default) = model.default_value(sort) {
        return Some(default);
    }
    match manager.sorts.get(sort).map(|s| &s.kind) {
        Some(SortKind::Bool) => Some(manager.mk_false()),
        Some(SortKind::Int) => Some(manager.mk_int(BigInt::from(0))),
        Some(SortKind::Real) => Some(manager.mk_real(Rational64::new(0, 1))),
        Some(SortKind::BitVec(width)) => Some(manager.mk_bitvec(BigInt::from(0), *width)),
        Some(SortKind::Uninterpreted(_)) => model.universe(sort).and_then(|u| u.first().copied()),
        _ => None,
    }
}

/// Collect every binder name nested inside `body` (the outer quantifier's
/// own variables are added by the caller).
///
/// Returns `Err` when the body contains a binder this engine cannot evaluate
/// (`Let`, `Match`): rebuilding those without substituting their bindings
/// would leave dangling variable references, so the whole check declines.
fn collect_nested_binder_names(
    body: TermId,
    manager: &TermManager,
    names: &mut FxHashSet<Spur>,
) -> Result<(), &'static str> {
    let mut stack: Vec<TermId> = vec![body];
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        if visited.len() > MAX_EVALUATED_BODY_SIZE {
            return Err("body too large");
        }
        let Some(node) = manager.get(term) else {
            return Err("dangling term id");
        };
        match &node.kind {
            TermKind::Forall { vars, body, .. } | TermKind::Exists { vars, body, .. } => {
                for &(name, _) in vars {
                    names.insert(name);
                }
                stack.push(*body);
                // Patterns are annotations, carried along when the quantifier
                // node is rebuilt and never evaluated as terms.
            }
            TermKind::Let { .. } => return Err("let binder in body"),
            TermKind::Match { .. } => return Err("match binder in body"),
            _ => {
                let mut children = ChildList::new();
                push_children(&node.kind, &mut children);
                stack.extend(children.iter().copied());
            }
        }
    }
    Ok(())
}

/// Push the immediate term children of `kind` onto `out`, in the canonical
/// positional order [`rebuild_with`] indexes them by.
///
/// Binders push only what this engine evaluates (a quantifier's body);
/// `Let`/`Match` are declined by the callers and push nothing.
fn push_children(kind: &TermKind, out: &mut ChildList) {
    match kind {
        TermKind::Forall { body, .. } | TermKind::Exists { body, .. } => out.push(*body),
        TermKind::Let { .. } | TermKind::Match { .. } => {}
        TermKind::Not(a) => out.push(*a),
        // Finite sets: ordinary children. Whether MBQI can *rebuild* them is
        // decided separately, in `rebuild`.
        TermKind::SetSingleton(a) | TermKind::SetCard(a) => out.push(*a),
        TermKind::SetUnion(a, b)
        | TermKind::SetInter(a, b)
        | TermKind::SetMinus(a, b)
        | TermKind::SetMember(a, b)
        | TermKind::SetSubset(a, b) => {
            out.push(*a);
            out.push(*b);
        }
        TermKind::SetEmpty(_) => {}
        TermKind::FfConst { .. } => {}
        TermKind::FfAdd(args) | TermKind::FfMul(args) | TermKind::FfBitsum(args) => {
            out.extend(args.iter().copied());
        }
        TermKind::FfNeg(a) => out.push(*a),
        TermKind::And(args) | TermKind::Or(args) | TermKind::Add(args) | TermKind::Mul(args) => {
            out.extend(args.iter().copied());
        }
        TermKind::Distinct(args) => out.extend(args.iter().copied()),
        TermKind::Apply { args, .. } | TermKind::DtConstructor { args, .. } => {
            out.extend(args.iter().copied());
        }
        TermKind::Xor(a, b)
        | TermKind::Implies(a, b)
        | TermKind::Eq(a, b)
        | TermKind::Sub(a, b)
        | TermKind::Div(a, b)
        | TermKind::Mod(a, b)
        | TermKind::Lt(a, b)
        | TermKind::Le(a, b)
        | TermKind::Gt(a, b)
        | TermKind::Ge(a, b)
        | TermKind::BvConcat(a, b)
        | TermKind::BvAnd(a, b)
        | TermKind::BvOr(a, b)
        | TermKind::BvXor(a, b)
        | TermKind::BvAdd(a, b)
        | TermKind::BvSub(a, b)
        | TermKind::BvMul(a, b)
        | TermKind::BvUdiv(a, b)
        | TermKind::BvSdiv(a, b)
        | TermKind::BvUrem(a, b)
        | TermKind::BvSrem(a, b)
        | TermKind::BvShl(a, b)
        | TermKind::BvLshr(a, b)
        | TermKind::BvAshr(a, b)
        | TermKind::BvUlt(a, b)
        | TermKind::BvUle(a, b)
        | TermKind::BvSlt(a, b)
        | TermKind::BvSle(a, b)
        | TermKind::StrConcat(a, b)
        | TermKind::StrAt(a, b)
        | TermKind::StrContains(a, b)
        | TermKind::StrPrefixOf(a, b)
        | TermKind::StrSuffixOf(a, b)
        | TermKind::StrInRe(a, b)
        | TermKind::StrLt(a, b)
        | TermKind::StrLe(a, b)
        | TermKind::FpRem(a, b)
        | TermKind::FpMin(a, b)
        | TermKind::FpMax(a, b)
        | TermKind::FpLeq(a, b)
        | TermKind::FpLt(a, b)
        | TermKind::FpGeq(a, b)
        | TermKind::FpGt(a, b)
        | TermKind::FpEq(a, b) => {
            out.push(*a);
            out.push(*b);
        }
        TermKind::Ite(c, t, e) | TermKind::Store(c, t, e) => {
            out.push(*c);
            out.push(*t);
            out.push(*e);
        }
        TermKind::StrSubstr(s, i, n)
        | TermKind::StrIndexOf(s, i, n)
        | TermKind::StrReplace(s, i, n)
        | TermKind::StrReplaceAll(s, i, n)
        | TermKind::StrReplaceRe(s, i, n)
        | TermKind::StrReplaceReAll(s, i, n) => {
            out.push(*s);
            out.push(*i);
            out.push(*n);
        }
        TermKind::Neg(a)
        | TermKind::StrLen(a)
        | TermKind::StrToInt(a)
        | TermKind::IntToStr(a)
        | TermKind::StrToCode(a)
        | TermKind::StrFromCode(a)
        | TermKind::BvNot(a)
        | TermKind::FpAbs(a)
        | TermKind::FpNeg(a)
        | TermKind::FpIsNormal(a)
        | TermKind::FpIsSubnormal(a)
        | TermKind::FpIsZero(a)
        | TermKind::FpIsInfinite(a)
        | TermKind::FpIsNaN(a)
        | TermKind::FpIsNegative(a)
        | TermKind::FpIsPositive(a)
        | TermKind::FpToReal(a)
        | TermKind::DtTester { arg: a, .. }
        | TermKind::DtSelector { arg: a, .. } => out.push(*a),
        TermKind::Select(a, i) => {
            out.push(*a);
            out.push(*i);
        }
        TermKind::BvExtract { arg, .. } => out.push(*arg),
        TermKind::FpSqrt(_, a) | TermKind::FpRoundToIntegral(_, a) => out.push(*a),
        TermKind::FpAdd(_, a, b)
        | TermKind::FpSub(_, a, b)
        | TermKind::FpMul(_, a, b)
        | TermKind::FpDiv(_, a, b) => {
            out.push(*a);
            out.push(*b);
        }
        TermKind::FpFma(_, a, b, c) => {
            out.push(*a);
            out.push(*b);
            out.push(*c);
        }
        TermKind::FpToFp { arg, .. }
        | TermKind::FpToSBV { arg, .. }
        | TermKind::FpToUBV { arg, .. }
        | TermKind::RealToFp { arg, .. }
        | TermKind::SBVToFp { arg, .. }
        | TermKind::UBVToFp { arg, .. } => out.push(*arg),
        TermKind::True
        | TermKind::False
        | TermKind::IntConst(_)
        | TermKind::RealConst(_)
        | TermKind::BitVecConst { .. }
        | TermKind::Var(_)
        | TermKind::StringLit(_)
        | TermKind::FpLit { .. }
        | TermKind::FpPlusInfinity { .. }
        | TermKind::FpMinusInfinity { .. }
        | TermKind::FpPlusZero { .. }
        | TermKind::FpMinusZero { .. }
        | TermKind::FpNaN { .. } => {}
    }
}

/// The completed-model evaluator (module docs, step 2).
struct CompletionEval<'a> {
    model: &'a CompletedModel,
    bound: &'a FxHashSet<Spur>,
    else_table: &'a FxHashMap<Spur, TermId>,
    cache: FxHashMap<TermId, TermId>,
    symbolic: FxHashMap<TermId, bool>,
    nodes_visited: usize,
    /// Current macro-unfolding nesting (see [`MAX_MACRO_DEPTH`]).
    macro_depth: u32,
}

/// Bound on macro-unfolding nesting inside one evaluation.  The
/// occurs-check in the macro solver forbids self-reference, so finite
/// nesting exists; the cap guards pathological mutual-macro chains and
/// keeps the native recursion in `fold_macro_application` bounded.
const MAX_MACRO_DEPTH: u32 = 16;

impl<'a> CompletionEval<'a> {
    /// Evaluate `root`; `Err` carries the decline reason.
    fn run(
        root: TermId,
        model: &'a CompletedModel,
        bound: &'a FxHashSet<Spur>,
        else_table: &'a FxHashMap<Spur, TermId>,
        manager: &mut TermManager,
    ) -> Result<TermId, &'static str> {
        let mut eval = Self {
            model,
            bound,
            else_table,
            cache: FxHashMap::default(),
            symbolic: FxHashMap::default(),
            nodes_visited: 0,
            macro_depth: 0,
        };
        eval.eval(root, manager)
    }

    /// Whether `term` (transitively) mentions a bound-variable name.
    ///
    /// Memoized post-order OR over the DAG; the explicit stack keeps deep
    /// bodies off the native call stack.  A frame short-circuits to `true`
    /// as soon as one child resolves `true`.  Frames carry only `Copy` data
    /// and are re-read from the stack each iteration, so pushing children
    /// mid-frame never fights a live borrow.
    fn is_symbolic(&mut self, term: TermId, manager: &TermManager) -> bool {
        if let Some(&known) = self.symbolic.get(&term) {
            return known;
        }
        // (node, next child index, OR of children resolved so far)
        let mut stack: Vec<(TermId, usize, bool)> = vec![(term, 0, false)];
        while let Some(&(node, next, acc)) = stack.last() {
            if acc {
                self.symbolic.insert(node, true);
                stack.pop();
                if let Some(frame) = stack.last_mut() {
                    frame.2 = true;
                }
                continue;
            }
            let Some(node_term) = manager.get(node) else {
                // Unknown id: conservatively concrete (the evaluator will
                // decline on it separately before anything is concluded).
                self.symbolic.insert(node, false);
                stack.pop();
                continue;
            };
            if let TermKind::Var(name) = &node_term.kind {
                let is_bound = self.bound.contains(name);
                self.symbolic.insert(node, is_bound);
                stack.pop();
                if is_bound && let Some(frame) = stack.last_mut() {
                    frame.2 = true;
                }
                continue;
            }
            let mut children = ChildList::new();
            push_children(&node_term.kind, &mut children);
            if next >= children.len() {
                self.symbolic.insert(node, acc);
                stack.pop();
                if acc && let Some(frame) = stack.last_mut() {
                    frame.2 = true;
                }
                continue;
            }
            let child = children[next];
            if let Some(frame) = stack.last_mut() {
                frame.1 = next + 1;
            }
            match self.symbolic.get(&child) {
                Some(&known) => {
                    if known && let Some(frame) = stack.last_mut() {
                        frame.2 = true;
                    }
                }
                None => stack.push((child, 0, false)),
            }
        }
        self.symbolic.get(&term).copied().unwrap_or(false)
    }

    /// Post-order evaluation with an explicit stack (deep bodies must not
    /// consume native stack; see AGENTS.md).
    fn eval(&mut self, root: TermId, manager: &mut TermManager) -> Result<TermId, &'static str> {
        enum Frame {
            Enter(TermId),
            Fold(TermId),
        }
        let mut stack: Vec<Frame> = vec![Frame::Enter(root)];
        // Values of already-folded children, innermost last.
        let mut values: Vec<TermId> = Vec::new();

        while let Some(frame) = stack.pop() {
            self.nodes_visited += 1;
            if self.nodes_visited > MAX_EVALUATED_BODY_SIZE {
                return Err("evaluated body too large");
            }
            match frame {
                Frame::Enter(term) => {
                    if let Some(&cached) = self.cache.get(&term) {
                        values.push(cached);
                        continue;
                    }
                    let Some(node) = manager.get(term).cloned() else {
                        return Err("dangling term id");
                    };
                    // Bound-variable occurrences stay symbolic *before* any
                    // model lookup: a declared constant sharing the bound
                    // variable's (name, sort) must not leak its value into a
                    // symbolic position.
                    if let TermKind::Var(name) = &node.kind
                        && self.bound.contains(name)
                    {
                        self.cache.insert(term, term);
                        values.push(term);
                        continue;
                    }
                    // Likewise, a *pinned* value may only be used for terms
                    // that are free of bound variables.  The model's
                    // assignment table also carries entries for terms that
                    // mention the bound variable (Tseitin/encoding
                    // artifacts like `(f3 f4 (+ f6 ?v0)) = 0`); honoring
                    // those would fix the variable's value and fabricate a
                    // satisfaction verdict (the round-1 false-`sat` shape).
                    if !self.is_symbolic(term, manager) {
                        if let Some(&value) = self.model.assignments.get(&term) {
                            self.cache.insert(term, value);
                            values.push(value);
                            continue;
                        }
                    }
                    match node.kind {
                        TermKind::Var(_) => {
                            // Unpinned free constant: kept as itself (its
                            // own representative in the nested goal).
                            self.cache.insert(term, term);
                            values.push(term);
                        }
                        TermKind::True
                        | TermKind::False
                        | TermKind::IntConst(_)
                        | TermKind::RealConst(_)
                        | TermKind::BitVecConst { .. }
                        | TermKind::StringLit(_)
                        | TermKind::FpLit { .. }
                        | TermKind::FpPlusInfinity { .. }
                        | TermKind::FpMinusInfinity { .. }
                        | TermKind::FpPlusZero { .. }
                        | TermKind::FpMinusZero { .. }
                        | TermKind::FpNaN { .. } => {
                            self.cache.insert(term, term);
                            values.push(term);
                        }
                        TermKind::Forall { body, .. } | TermKind::Exists { body, .. } => {
                            stack.push(Frame::Fold(term));
                            stack.push(Frame::Enter(body));
                        }
                        TermKind::Apply { args, .. } => {
                            stack.push(Frame::Fold(term));
                            for &arg in args.iter().rev() {
                                stack.push(Frame::Enter(arg));
                            }
                        }
                        TermKind::Let { .. } => return Err("let binder in body"),
                        TermKind::Match { .. } => return Err("match binder in body"),
                        kind => {
                            stack.push(Frame::Fold(term));
                            let mut children = ChildList::new();
                            push_children(&kind, &mut children);
                            for &child in children.iter().rev() {
                                stack.push(Frame::Enter(child));
                            }
                        }
                    }
                }
                Frame::Fold(term) => {
                    let Some(node) = manager.get(term).cloned() else {
                        return Err("dangling term id");
                    };
                    let mut probe = ChildList::new();
                    push_children(&node.kind, &mut probe);
                    let arity = probe.len();
                    if values.len() < arity {
                        return Err("evaluator stack underflow");
                    }
                    let evaluated: Vec<TermId> = values.split_off(values.len() - arity);
                    let result = match &node.kind {
                        TermKind::Apply { func, .. } => {
                            self.fold_apply(*func, &evaluated, node.sort, manager)?
                        }
                        TermKind::Forall { vars, patterns, .. } => {
                            let folded = evaluated.first().copied().unwrap_or(term);
                            manager.intern_term(
                                TermKind::Forall {
                                    vars: vars.clone(),
                                    body: folded,
                                    patterns: patterns.clone(),
                                },
                                node.sort,
                            )
                        }
                        TermKind::Exists { vars, patterns, .. } => {
                            let folded = evaluated.first().copied().unwrap_or(term);
                            // Dually: `exists x. c` is `c` for a pointwise
                            // constant body (`exists x. false` refuted the
                            // A2 axiom's witness under the completion, and
                            // the un-mined falsifier froze the loop).
                            if manager
                                .get(folded)
                                .is_some_and(|t| matches!(t.kind, TermKind::True | TermKind::False))
                            {
                                folded
                            } else {
                                manager.intern_term(
                                    TermKind::Exists {
                                        vars: vars.clone(),
                                        body: folded,
                                        patterns: patterns.clone(),
                                    },
                                    node.sort,
                                )
                            }
                        }
                        TermKind::Eq(..) => {
                            let (a, b) = two(&evaluated);
                            if a == b {
                                manager.mk_true()
                            } else {
                                match compare_numeric(a, b, manager) {
                                    Some(NumOrder::Eq) => manager.mk_true(),
                                    Some(_) => manager.mk_false(),
                                    None => {
                                        // Uninterpreted-sort equality: two
                                        // *distinct universe representatives*
                                        // of the same sort are unequal by
                                        // construction (the universe is a
                                        // set of pairwise-distinct
                                        // elements).  Without this fold the
                                        // ite-chain conditions `(= z a)` of
                                        // a mined substitution stay symbolic
                                        // and the falsifier the aux check
                                        // found at `(z,z)` is never mined
                                        // (the set-family diagonal stall).
                                        let verdict = (|| {
                                            let na = manager.get(a)?;
                                            let nb = manager.get(b)?;
                                            if na.sort != nb.sort
                                                || !matches!(
                                                    manager.sorts.get(na.sort).map(|s| &s.kind),
                                                    Some(SortKind::Uninterpreted(_)),
                                                )
                                            {
                                                return None;
                                            }
                                            let uni = self.model.universe(na.sort)?;
                                            let a_in = uni.contains(&a);
                                            let b_in = uni.contains(&b);
                                            (a_in && b_in).then_some(false)
                                        })();
                                        match verdict {
                                            Some(false) => manager.mk_false(),
                                            _ => manager.mk_eq(a, b),
                                        }
                                    }
                                }
                            }
                        }
                        TermKind::Neg(..) => {
                            let a = evaluated[0];
                            if let Some(v) = numeric_value(a, manager) {
                                let is_real = manager
                                    .get(a)
                                    .is_some_and(|n| n.sort == manager.sorts.real_sort);
                                mk_numeric(-v, is_real, manager)
                                    .unwrap_or_else(|| manager.mk_neg(a))
                            } else {
                                rebuild_with(&node.kind, &evaluated, node.sort, manager)?
                            }
                        }
                        TermKind::Add(..) => {
                            // Fold the numeric constants among the operands
                            // so concrete instantiations resolve chain
                            // conditions (`(+ f6 c)` vs an entry's value).
                            let mut sum = Rational64::zero();
                            let mut rest: Vec<TermId> = Vec::new();
                            let mut is_real = node.sort == manager.sorts.real_sort;
                            for &a in &evaluated {
                                if let Some(v) = numeric_value(a, manager) {
                                    sum += v;
                                    if manager
                                        .get(a)
                                        .is_some_and(|n| n.sort == manager.sorts.real_sort)
                                    {
                                        is_real = true;
                                    }
                                } else {
                                    rest.push(a);
                                }
                            }
                            if rest.is_empty() {
                                mk_numeric(sum, is_real, manager)
                                    .unwrap_or_else(|| manager.mk_add(evaluated.clone()))
                            } else if sum != Rational64::zero()
                                && let Some(sum_term) = mk_numeric(sum, is_real, manager)
                            {
                                let mut parts = rest;
                                parts.push(sum_term);
                                manager.mk_add(parts)
                            } else {
                                manager.mk_add(rest)
                            }
                        }
                        TermKind::Sub(..) => {
                            let (a, b) = two(&evaluated);
                            match (numeric_value(a, manager), numeric_value(b, manager)) {
                                (Some(x), Some(y)) => {
                                    let is_real = node.sort == manager.sorts.real_sort;
                                    mk_numeric(x - y, is_real, manager)
                                        .unwrap_or_else(|| manager.mk_sub(a, b))
                                }
                                _ => rebuild_with(&node.kind, &evaluated, node.sort, manager)?,
                            }
                        }
                        TermKind::Mul(..) => {
                            let mut product = Rational64::one();
                            let mut rest: Vec<TermId> = Vec::new();
                            let mut is_real = node.sort == manager.sorts.real_sort;
                            for &a in &evaluated {
                                if let Some(v) = numeric_value(a, manager) {
                                    product *= v;
                                    if manager
                                        .get(a)
                                        .is_some_and(|n| n.sort == manager.sorts.real_sort)
                                    {
                                        is_real = true;
                                    }
                                } else {
                                    rest.push(a);
                                }
                            }
                            if rest.is_empty() {
                                mk_numeric(product, is_real, manager)
                                    .unwrap_or_else(|| manager.mk_mul(evaluated.clone()))
                            } else if product != Rational64::one()
                                && let Some(prod_term) = mk_numeric(product, is_real, manager)
                            {
                                let mut parts = rest;
                                parts.push(prod_term);
                                manager.mk_mul(parts)
                            } else {
                                manager.mk_mul(rest)
                            }
                        }
                        TermKind::Lt(..)
                        | TermKind::Le(..)
                        | TermKind::Gt(..)
                        | TermKind::Ge(..) => {
                            let (a, b) = two(&evaluated);
                            if a == b {
                                if matches!(node.kind, TermKind::Le(..) | TermKind::Ge(..)) {
                                    manager.mk_true()
                                } else {
                                    manager.mk_false()
                                }
                            } else {
                                match compare_numeric(a, b, manager)
                                    .map(|order| order_satisfies(&node.kind, order))
                                {
                                    Some(true) => manager.mk_true(),
                                    Some(false) => manager.mk_false(),
                                    None => {
                                        rebuild_with(&node.kind, &evaluated, node.sort, manager)?
                                    }
                                }
                            }
                        }
                        _ => rebuild_with(&node.kind, &evaluated, node.sort, manager)?,
                    };
                    self.cache.insert(term, result);
                    values.push(result);
                }
            }
        }

        values.pop().ok_or("evaluator produced no value")
    }

    /// Beta-reduce a macro body at the evaluated arguments and evaluate the
    /// result under the same completion.  The body's free variables are the
    /// macro's bound variables; substituting the arguments grounds it.
    fn fold_macro_application(
        &mut self,
        bound_vars: &[(Spur, SortId)],
        body: TermId,
        evaluated_args: &[TermId],
        manager: &mut TermManager,
    ) -> Result<TermId, &'static str> {
        if bound_vars.len() != evaluated_args.len() {
            // Arity mismatch: the macro solver's shape guarantee is broken;
            // decline rather than mis-substitute.
            return Err("macro arity mismatch");
        }
        let mut subst: FxHashMap<TermId, TermId> = FxHashMap::default();
        for (&(name, sort), &arg) in bound_vars.iter().zip(evaluated_args.iter()) {
            let name_str = manager.resolve_str(name).to_string();
            let var = manager.mk_var(&name_str, sort);
            subst.insert(var, arg);
        }
        let reduced = manager.substitute(body, &subst);
        // Evaluate the reduced body to a value with the same machine.
        // Bound-name hygiene: the macro's own binders were substituted away;
        // any *other* free names in the body are the enclosing scope's —
        // exactly what `self.bound` tracks.
        self.nodes_visited += 1;
        if self.nodes_visited > MAX_EVALUATED_BODY_SIZE {
            return Err("evaluated body too large");
        }
        self.eval(reduced, manager)
    }

    /// Fold one function application under the completed interpretation.
    fn fold_apply(
        &mut self,
        func: Spur,
        evaluated_args: &[TermId],
        sort: SortId,
        manager: &mut TermManager,
    ) -> Result<TermId, &'static str> {
        // Macro completion first: a function with a defining axiom
        // (`seteq(s1,s2) = (s1 = s2)`) is interpreted by beta-reducing its
        // body at the (already evaluated) arguments and evaluating the
        // result under the same completion.  Entries stay authoritative
        // when present — the macro fills the *rest* of the domain, which is
        // exactly what per-element pinning could never close (a definitional
        // axiom fails at every unpinned reflexive point, however many pins
        // the seeding adds).
        if let Some((bound_vars, body)) = self.model.macros.get(&func).cloned() {
            if self.macro_depth < MAX_MACRO_DEPTH {
                self.macro_depth += 1;
                let result =
                    self.fold_macro_application(&bound_vars, body, evaluated_args, manager);
                self.macro_depth -= 1;
                return result;
            }
            // Macro nesting too deep: decline rather than evaluate through
            // an interpretation we cannot afford to unfold.
            return Err("macro nesting too deep");
        }
        let interp = self.model.function_interps.get(&func);
        let all_concrete = !evaluated_args
            .iter()
            .any(|&arg| self.is_symbolic(arg, manager));

        if all_concrete {
            // Entry lookup on normalized values; a miss falls to the else.
            if let Some(interp) = interp {
                for entry in &interp.entries {
                    if args_match(entry, evaluated_args, self.model, manager) {
                        return Ok(entry.result);
                    }
                }
            }
            if let Some(&else_val) = self.else_table.get(&func) {
                return Ok(else_val);
            }
            // No interpretation and no else: keep the application as a free
            // ground term (unconstrained by the model; the nested solver
            // sees it as itself).
            let args: ChildList = evaluated_args.iter().copied().collect();
            return Ok(manager.intern_term(TermKind::Apply { func, args }, sort));
        }

        // Symbolic argument: the entry table as an ite chain, else leaf.
        let else_leaf = match self.else_table.get(&func) {
            Some(&else_val) => else_val,
            None => {
                // A function the completion pass never saw still needs a
                // total interpretation; the application's own sort is the
                // range.  Choosing it here is an interpretation decision
                // the nested check verifies, never a fabricated fact.
                sort_default(sort, self.model, manager).ok_or("no else for symbolic application")?
            }
        };
        let Some(interp) = interp else {
            return Ok(else_leaf);
        };
        let mut acc = else_leaf;
        for entry in interp.entries.iter().rev() {
            // Encoding artifacts: an entry indexed by a bound-variable
            // mentioning argument is not a fact about the completed
            // interpretation (the bound variable is not a domain element
            // of this check), and its condition could never legitimately
            // fire.  Skip it.
            if entry.args.iter().any(|&a| self.is_symbolic(a, manager)) {
                continue;
            }
            // Redundant entry: a result equal to the else leaf is subsumed
            // by it.  The enumerative seeder pins the function at every
            // fresh candidate point (each round's new Real index terms),
            // and when those pins agree with the closed-world default they
            // are pure noise — thousands of `member(x, s) = false` entries
            // that bury the structural pins and blow the ite chain past
            // every cap (the set16 divergence).
            if value_equal(entry.result, else_leaf, manager) == Some(true) {
                continue;
            }
            // Skip entries a concrete evaluated argument can never hit.
            let mut reachable = true;
            let mut conditions: Vec<TermId> = Vec::new();
            for (i, &arg) in evaluated_args.iter().enumerate() {
                let Some(&entry_arg) = entry.args.get(i) else {
                    reachable = false;
                    break;
                };
                let entry_norm = self
                    .model
                    .assignments
                    .get(&entry_arg)
                    .copied()
                    .unwrap_or(entry_arg);
                if arg == entry_norm {
                    continue; // trivially equal
                }
                if !self.is_symbolic(arg, manager) {
                    // Compare values exactly; unequal concrete arguments
                    // make this entry unreachable.
                    match value_equal(arg, entry_norm, manager) {
                        Some(true) => continue,
                        Some(false) => {
                            reachable = false;
                            break;
                        }
                        None => { /* not comparable here; let the solver decide */ }
                    }
                }
                conditions.push(manager.mk_eq(arg, entry_norm));
            }
            if !reachable {
                continue;
            }
            if conditions.is_empty() {
                // Every argument position is trivially equal: the entry is
                // the value outright (deeper entries are shadowed).
                return Ok(entry.result);
            }
            let cond = if conditions.len() == 1 {
                conditions[0]
            } else {
                manager.mk_and(conditions)
            };
            acc = manager.mk_ite(cond, entry.result, acc);
        }
        Ok(acc)
    }
}

/// Rebuild a node with folded children.
///
/// Mirrors `TermManager`'s substitution rebuild one-for-one (same
/// constructors, exhaustive over `TermKind`): hash-consing makes an
/// unchanged rebuild return the original `TermId`.
fn rebuild_with(
    kind: &TermKind,
    evaluated: &[TermId],
    sort: SortId,
    manager: &mut TermManager,
) -> Result<TermId, &'static str> {
    let one = |i: usize| -> Result<TermId, &'static str> {
        evaluated.get(i).copied().ok_or("missing child")
    };
    let two_at =
        |i: usize| -> Result<(TermId, TermId), &'static str> { Ok((one(i)?, one(i + 1)?)) };
    let nary = |n: usize| -> Result<ChildList, &'static str> { (0..n).map(one).collect() };
    Ok(match kind {
        TermKind::True
        | TermKind::False
        | TermKind::IntConst(_)
        | TermKind::RealConst(_)
        | TermKind::BitVecConst { .. }
        | TermKind::Var(_)
        | TermKind::StringLit(_)
        | TermKind::FpLit { .. }
        | TermKind::FpPlusInfinity { .. }
        | TermKind::FpMinusInfinity { .. }
        | TermKind::FpPlusZero { .. }
        | TermKind::FpMinusZero { .. }
        | TermKind::FpNaN { .. }
        | TermKind::FfConst { .. } => {
            return Err("leaf scheduled as fold");
        }
        TermKind::Let { .. } | TermKind::Match { .. } => return Err("binder in rebuild"),
        TermKind::Forall { .. } | TermKind::Exists { .. } => {
            return Err("quantifier handled by its own fold");
        }

        // Finite fields: rebuilt through the total normal-form helper (the
        // fallible constructors cannot fail on interned nodes; see
        // `intern_ff_substituted`).
        TermKind::FfAdd(args) => {
            manager.intern_ff_substituted(TermKind::FfAdd(nary(args.len())?), sort)
        }
        TermKind::FfMul(args) => {
            manager.intern_ff_substituted(TermKind::FfMul(nary(args.len())?), sort)
        }
        TermKind::FfBitsum(args) => {
            manager.intern_ff_substituted(TermKind::FfBitsum(nary(args.len())?), sort)
        }
        TermKind::FfNeg(_) => manager.intern_ff_substituted(kind.clone(), sort),
        TermKind::Not(_) => manager.mk_not(one(0)?),
        TermKind::And(args) => manager.mk_and(nary(args.len())?),
        TermKind::Or(args) => manager.mk_or(nary(args.len())?),
        TermKind::Xor(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_xor(a, b)
        }
        TermKind::Implies(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_implies(a, b)
        }
        TermKind::Ite(..) => manager.mk_ite(one(0)?, one(1)?, one(2)?),
        TermKind::Distinct(args) => manager.mk_distinct(nary(args.len())?),
        TermKind::Eq(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_eq(a, b)
        }
        TermKind::Neg(_) => manager.mk_neg(one(0)?),
        TermKind::Add(args) => manager.mk_add(nary(args.len())?),
        TermKind::Sub(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_sub(a, b)
        }
        TermKind::Mul(args) => manager.mk_mul(nary(args.len())?),
        TermKind::Div(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_div(a, b)
        }
        TermKind::Mod(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_mod(a, b)
        }
        TermKind::Lt(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_lt(a, b)
        }
        TermKind::Le(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_le(a, b)
        }
        TermKind::Gt(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_gt(a, b)
        }
        TermKind::Ge(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_ge(a, b)
        }
        TermKind::Select(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_select(a, b)
        }
        TermKind::Store(..) => manager.mk_store(one(0)?, one(1)?, one(2)?),
        TermKind::BvConcat(..) => {
            let (a, b) = two_at(0)?;
            manager
                .try_mk_bv_concat(a, b)
                .unwrap_or_else(|_| manager.intern_term(TermKind::BvConcat(a, b), sort))
        }
        TermKind::BvExtract { high, low, .. } => manager.mk_bv_extract(*high, *low, one(0)?),
        TermKind::BvNot(_) => manager.mk_bv_not(one(0)?),
        TermKind::BvAnd(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bv_and(a, b)
        }
        TermKind::BvOr(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bv_or(a, b)
        }
        TermKind::BvXor(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bv_xor(a, b)
        }
        TermKind::BvAdd(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bv_add(a, b)
        }
        TermKind::BvSub(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bv_sub(a, b)
        }
        TermKind::BvMul(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bv_mul(a, b)
        }
        TermKind::BvUdiv(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bv_udiv(a, b)
        }
        TermKind::BvSdiv(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bv_sdiv(a, b)
        }
        TermKind::BvUrem(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bv_urem(a, b)
        }
        TermKind::BvSrem(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bv_srem(a, b)
        }
        TermKind::BvShl(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bv_shl(a, b)
        }
        TermKind::BvLshr(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bv_lshr(a, b)
        }
        TermKind::BvAshr(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bv_ashr(a, b)
        }
        TermKind::BvUlt(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bv_ult(a, b)
        }
        TermKind::BvUle(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bv_ule(a, b)
        }
        TermKind::BvSlt(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bv_slt(a, b)
        }
        TermKind::BvSle(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bv_sle(a, b)
        }

        // Finite sets rebuild structurally; `set.member` and `set.subset` are
        // the ones whose *truth* needs a theory, and there is none yet, so the
        // model checker declines rather than evaluating them to a guess.
        TermKind::SetEmpty(sort) => manager.mk_set_empty_at(*sort),
        TermKind::SetSingleton(_) => manager.mk_set_singleton(one(0)?),
        TermKind::SetUnion(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_set_union(a, b)
        }
        TermKind::SetInter(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_set_inter(a, b)
        }
        TermKind::SetMinus(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_set_minus(a, b)
        }
        TermKind::SetMember(..) | TermKind::SetSubset(..) | TermKind::SetCard(_) => {
            return Err("set predicate has no theory to evaluate it");
        }
        TermKind::StrConcat(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_str_concat(a, b)
        }
        TermKind::StrLen(_) => manager.mk_str_len(one(0)?),
        TermKind::StrSubstr(..) => manager.mk_str_substr(one(0)?, one(1)?, one(2)?),
        TermKind::StrAt(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_str_at(a, b)
        }
        TermKind::StrContains(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_str_contains(a, b)
        }
        TermKind::StrPrefixOf(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_str_prefixof(a, b)
        }
        TermKind::StrSuffixOf(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_str_suffixof(a, b)
        }
        TermKind::StrIndexOf(..) => manager.mk_str_indexof(one(0)?, one(1)?, one(2)?),
        TermKind::StrReplace(..) => manager.mk_str_replace(one(0)?, one(1)?, one(2)?),
        TermKind::StrReplaceAll(..) => manager.mk_str_replace_all(one(0)?, one(1)?, one(2)?),
        TermKind::StrReplaceRe(..) => manager.mk_str_replace_re(one(0)?, one(1)?, one(2)?),
        TermKind::StrReplaceReAll(..) => manager.mk_str_replace_re_all(one(0)?, one(1)?, one(2)?),
        TermKind::StrToInt(_) => manager.mk_str_to_int(one(0)?),
        TermKind::IntToStr(_) => manager.mk_int_to_str(one(0)?),
        TermKind::StrInRe(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_str_in_re(a, b)
        }
        TermKind::StrLt(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_str_lt(a, b)
        }
        TermKind::StrLe(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_str_le(a, b)
        }
        TermKind::StrToCode(_) => manager.mk_str_to_code(one(0)?),
        TermKind::StrFromCode(_) => manager.mk_str_from_code(one(0)?),

        TermKind::FpAbs(_) => manager.mk_fp_abs(one(0)?),
        TermKind::FpNeg(_) => manager.mk_fp_neg(one(0)?),
        TermKind::FpSqrt(rm, _) => manager.mk_fp_sqrt(*rm, one(0)?),
        TermKind::FpRoundToIntegral(rm, _) => manager.mk_fp_round_to_integral(*rm, one(0)?),
        TermKind::FpAdd(rm, ..) => manager.mk_fp_add(*rm, one(0)?, one(1)?),
        TermKind::FpSub(rm, ..) => manager.mk_fp_sub(*rm, one(0)?, one(1)?),
        TermKind::FpMul(rm, ..) => manager.mk_fp_mul(*rm, one(0)?, one(1)?),
        TermKind::FpDiv(rm, ..) => manager.mk_fp_div(*rm, one(0)?, one(1)?),
        TermKind::FpRem(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_fp_rem(a, b)
        }
        TermKind::FpMin(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_fp_min(a, b)
        }
        TermKind::FpMax(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_fp_max(a, b)
        }
        TermKind::FpLeq(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_fp_leq(a, b)
        }
        TermKind::FpLt(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_fp_lt(a, b)
        }
        TermKind::FpGeq(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_fp_geq(a, b)
        }
        TermKind::FpGt(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_fp_gt(a, b)
        }
        TermKind::FpEq(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_fp_eq(a, b)
        }
        TermKind::FpFma(rm, ..) => manager.mk_fp_fma(*rm, one(0)?, one(1)?, one(2)?),
        TermKind::FpIsNormal(_) => manager.mk_fp_is_normal(one(0)?),
        TermKind::FpIsSubnormal(_) => manager.mk_fp_is_subnormal(one(0)?),
        TermKind::FpIsZero(_) => manager.mk_fp_is_zero(one(0)?),
        TermKind::FpIsInfinite(_) => manager.mk_fp_is_infinite(one(0)?),
        TermKind::FpIsNaN(_) => manager.mk_fp_is_nan(one(0)?),
        TermKind::FpIsNegative(_) => manager.mk_fp_is_negative(one(0)?),
        TermKind::FpIsPositive(_) => manager.mk_fp_is_positive(one(0)?),
        TermKind::FpToReal(_) => manager.mk_fp_to_real(one(0)?),
        TermKind::FpToFp { rm, eb, sb, .. } => manager.mk_fp_to_fp(*rm, one(0)?, *eb, *sb),
        TermKind::FpToSBV { rm, width, .. } => manager.mk_fp_to_sbv(*rm, one(0)?, *width),
        TermKind::FpToUBV { rm, width, .. } => manager.mk_fp_to_ubv(*rm, one(0)?, *width),
        TermKind::RealToFp { rm, eb, sb, .. } => manager.mk_real_to_fp(*rm, one(0)?, *eb, *sb),
        TermKind::SBVToFp { rm, eb, sb, .. } => manager.mk_sbv_to_fp(*rm, one(0)?, *eb, *sb),
        TermKind::UBVToFp { rm, eb, sb, .. } => manager.mk_ubv_to_fp(*rm, one(0)?, *eb, *sb),

        TermKind::Apply { func, .. } => {
            let args: ChildList = evaluated.iter().copied().collect();
            manager.intern_term(TermKind::Apply { func: *func, args }, sort)
        }
        TermKind::DtConstructor { constructor, .. } => {
            let args: ChildList = evaluated.iter().copied().collect();
            manager.intern_term(
                TermKind::DtConstructor {
                    constructor: *constructor,
                    args,
                },
                sort,
            )
        }
        TermKind::DtTester { constructor, .. } => manager.intern_term(
            TermKind::DtTester {
                constructor: *constructor,
                arg: one(0)?,
            },
            sort,
        ),
        TermKind::DtSelector { selector, .. } => manager.intern_term(
            TermKind::DtSelector {
                selector: *selector,
                arg: one(0)?,
            },
            sort,
        ),
    })
}

/// Two values off the evaluated-children slice.
fn two(evaluated: &[TermId]) -> (TermId, TermId) {
    (evaluated[0], evaluated[1])
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NumOrder {
    Lt,
    Eq,
    Gt,
}

/// Exact numeric order between two value terms, when both are numeric
/// literals (`IntConst`/`RealConst`, mixed allowed).  `None` when not
/// comparable (non-numeric, or a magnitude that does not fit `i64`
/// exactly — never truncate: the nested solver decides those).
fn compare_numeric(a: TermId, b: TermId, manager: &TermManager) -> Option<NumOrder> {
    let ra = numeric_value(a, manager)?;
    let rb = numeric_value(b, manager)?;
    match ra.cmp(&rb) {
        core::cmp::Ordering::Less => Some(NumOrder::Lt),
        core::cmp::Ordering::Equal => Some(NumOrder::Eq),
        core::cmp::Ordering::Greater => Some(NumOrder::Gt),
    }
}

/// Exact rational value of a numeric literal term, when representable.
fn numeric_value(term: TermId, manager: &TermManager) -> Option<Rational64> {
    match manager.get(term).map(|t| &t.kind) {
        Some(TermKind::IntConst(n)) => {
            // Exact conversion only: a BigInt outside i64 declines rather
            // than truncates (AGENTS.md: bignums are exact).
            Some(Rational64::new(n.to_i64()?, 1))
        }
        Some(TermKind::RealConst(r)) => Some(*r),
        _ => None,
    }
}

/// Build a numeric literal of the given flavor from an exact rational, or
/// `None` when the value is not exactly representable (a non-integral
/// rational for an integer literal, or a magnitude outside the manager's
/// rational range).  Callers fall back to rebuilding the node — never a
/// truncated value.
fn mk_numeric(value: Rational64, is_real: bool, manager: &mut TermManager) -> Option<TermId> {
    if is_real {
        Some(manager.mk_real(value))
    } else {
        if value.is_integer()
            && let Some(bi) = value.numer().to_i64()
        {
            Some(manager.mk_int(BigInt::from(bi)))
        } else {
            None
        }
    }
}

/// Whether two value terms are certainly equal (`Some`), certainly unequal
/// (`Some(false)`), or not decidable here (`None`).
fn value_equal(a: TermId, b: TermId, manager: &TermManager) -> Option<bool> {
    if a == b {
        return Some(true);
    }
    match (manager.get(a), manager.get(b)) {
        (Some(na), Some(nb)) => match (&na.kind, &nb.kind) {
            (TermKind::IntConst(x), TermKind::IntConst(y)) => Some(x == y),
            (TermKind::RealConst(x), TermKind::RealConst(y)) => Some(x == y),
            (TermKind::IntConst(x), TermKind::RealConst(y)) => {
                Some(Rational64::new(x.to_i64()?, 1) == *y)
            }
            (TermKind::RealConst(x), TermKind::IntConst(y)) => {
                Some(*x == Rational64::new(y.to_i64()?, 1))
            }
            (TermKind::True, TermKind::True) | (TermKind::False, TermKind::False) => Some(true),
            (TermKind::True, TermKind::False) | (TermKind::False, TermKind::True) => Some(false),
            (
                TermKind::BitVecConst {
                    value: v1,
                    width: w1,
                },
                TermKind::BitVecConst {
                    value: v2,
                    width: w2,
                },
            ) => Some(v1 == v2 && w1 == w2),
            _ => None,
        },
        _ => None,
    }
}

/// Whether a comparison kind is satisfied by the given numeric order.
fn order_satisfies(kind: &TermKind, order: NumOrder) -> bool {
    match kind {
        TermKind::Lt(..) => order == NumOrder::Lt,
        TermKind::Le(..) => order != NumOrder::Gt,
        TermKind::Gt(..) => order == NumOrder::Gt,
        TermKind::Ge(..) => order != NumOrder::Lt,
        _ => false,
    }
}

/// Whether an entry's (normalized) arguments match fully concrete evaluated
/// arguments.
fn args_match(
    entry: &FunctionEntry,
    evaluated_args: &[TermId],
    model: &CompletedModel,
    manager: &TermManager,
) -> bool {
    if entry.args.len() != evaluated_args.len() {
        return false;
    }
    for (i, &arg) in evaluated_args.iter().enumerate() {
        let entry_arg = entry.args[i];
        let entry_norm = model
            .assignments
            .get(&entry_arg)
            .copied()
            .unwrap_or(entry_arg);
        match value_equal(arg, entry_norm, manager) {
            Some(true) => {}
            _ => return false,
        }
    }
    true
}
