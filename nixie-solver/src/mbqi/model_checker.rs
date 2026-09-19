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

pub(crate) type ChildList = SmallVec<[TermId; 4]>;

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

/// Hard *total* bound on nested solves per quantifier per solve (no
/// reset): see the streak comment at its use site — a converging
/// quantifier may reset its wasted-solve streak, but never past this
/// many solves in one `ModelChecker` lifetime.
const MAX_TOTAL_CHECKS_PER_QUANTIFIER: u32 = 4;

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

/// The current model-checker nesting depth (0 = the outer solver's MBQI).
pub(crate) fn nested_depth() -> u32 {
    NESTED_DEPTH.load(Ordering::Acquire)
}

/// One falsifier mined from a completed model, with the evidence its
/// evaluation rested on (see [`ModelChecker::check`]).
#[derive(Debug)]
pub(crate) struct MinedFalsifier {
    /// Bound-variable name -> ground falsifying term.
    pub(crate) substitution: FxHashMap<Spur, TermId>,
    /// The ground atoms whose completed values this falsifier's evaluation
    /// consumed: `(atom, value)` pairs, `atom` a Bool-sorted term and
    /// `value` its completed truth value (a `True`/`False` term).  Used to
    /// build the Z3-style blocking clause (`add_blocking_clause`): the
    /// arrangement "every one of these atoms takes exactly this value"
    /// demonstrably fails the quantifier, so excluding it from the next
    /// candidate model is sound (see `fully_pinned`).
    pub(crate) commitments: Vec<(TermId, TermId)>,
    /// Whether the evaluation consumed *only* recorded commitments — every
    /// function application resolved through an entry or an assignment hit,
    /// no `else` fallthrough, macro expansion, sort default or universe
    /// fold.  Only then is the falsification a function of the commitments
    /// alone, and only then may a blocking clause over them be emitted: a
    /// falsifier that leaned on a free completion choice can be repaired by
    /// revising the completion instead, and blocking the ground-visible part
    /// of such an arrangement could exclude a genuine solution.
    pub(crate) fully_pinned: bool,
}

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
        /// The mined falsifiers, one per falsifying combination.
        falsifiers: Vec<MinedFalsifier>,
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
    /// Wasted-solve streak per quantifier (see [`MAX_CHECKS_PER_QUANTIFIER`]):
    /// incremented only when a nested solve produced neither a fresh
    /// instantiation (the caller refunds via [`ModelChecker::mark_productive`])
    /// nor a satisfaction verdict; reset by either.
    checks_of: FxHashMap<TermId, u32>,
    /// Total nested solves per quantifier (never reset — see
    /// [`MAX_TOTAL_CHECKS_PER_QUANTIFIER`]).
    total_checks_of: FxHashMap<TermId, u32>,
    /// Whether constructor/hint tables are active (see
    /// [`Self::set_table_mode`]).
    table_mode: bool,
    /// Model signatures at which the nested refutation *certified* the
    /// quantifier (the aux-`unsat` verdict, possibly via the closed-world
    /// else retry).  The dual of [`ModelChecker::falsified_at`]: a
    /// certification is model-relative, so it is remembered per signature
    /// — a later round against the *same* completed model reuses it
    /// without re-paying the nested solve, and a moved model re-earns it.
    certified_at: FxHashMap<TermId, Vec<u64>>,
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
            total_checks_of: FxHashMap::default(),
            table_mode: false,
            certified_at: FxHashMap::default(),
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

    /// Cumulative aux conflicts spent so far (diagnostic).
    pub(crate) fn cumulative_aux_conflicts(&self) -> u64 {
        self.conflicts_spent
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

    /// The convergence dividend: a round that produced *no* fresh
    /// instantiation anywhere is the static-model signal — the per-
    /// quantifier caps exist to bound waste on a *moving* model (the
    /// chase), and by now their remaining budget is exactly what silences
    /// the certification wave that would close the search.  Refund both
    /// maps (streak and total) once per barren round; the *global* caps
    /// (`checks_performed`, `conflicts_spent`) are not refunded, so a
    /// pathological loop still terminates.
    pub(crate) fn refund_on_barren_round(&mut self) {
        if !self.table_mode || (self.checks_of.is_empty() && self.total_checks_of.is_empty()) {
            return;
        }
        if std::env::var_os("NIXIE_DEBUG_MC").is_some() {
            eprintln!("[mc] barren round: refunding per-quantifier check budgets");
        }
        self.checks_of.clear();
        self.total_checks_of.clear();
    }

    /// Whether constructor/hint tables are active this round (set by the
    /// integration from `active_table_quantifiers`).  The budget-refund
    /// mechanics below exist to let a *table-driven* convergence run its
    /// certification waves; on goals with no tables the old cap behaviour
    /// stands (the refunds there only stretched re-checked goals — the
    /// scope-rebase convergence pins).
    pub(crate) fn set_table_mode(&mut self, active: bool) {
        self.table_mode = active;
    }

    pub(crate) fn mark_productive(&mut self, quantifier: TermId) {
        self.last_model_signature.remove(&quantifier);
        // Productive-check refund of the wasted-solve streak: a check that
        // produced a fresh instantiation paid for itself, and a quantifier
        // that keeps producing is exactly the one the streak cap should
        // not silence mid-convergence (the set family's definitional axioms
        // mine one diagonal per round against a moving model).  The global
        // budgets still bound the total, so the refund cannot unbound a
        // single solve.
        self.checks_of.insert(quantifier, 0);
        // ...and of the per-quantifier *total* (table mode only): the
        // total exists to bound waste, not work — a check whose falsifiers
        // became fresh lemmas (or whose certification landed, below) moved
        // the search forward, and charging it would silence exactly the
        // converging quantifiers (the set family: every round's pin wave
        // moves the model, every re-check is productive, and a hard total
        // of four stops the loop mid-convergence).  The global budgets
        // remain the real bound.  Without tables the old cap behaviour
        // stands — the refund there only stretched re-checked goals.
        if self.table_mode
            && let Some(count) = self.total_checks_of.get_mut(&quantifier)
        {
            *count = count.saturating_sub(1);
        }
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
        // Wasted-solve streak per quantifier: the global budgets bound the
        // total, but a forced rerun's model can *move* (learned clauses
        // change the search) on every one of its hundreds of reruns, each
        // move re-arming the same-model gate.  Only *wasted* solves count
        // (a duplicate-falsifier solve, a liar's empty counterexample);
        // fresh lemmas and certifications reset the streak — a converging
        // quantifier never hits the cap, a doomed one stops re-paying.
        //
        // The landed accounting is a streak with a *hard total* underneath
        // (`MAX_TOTAL_CHECKS_PER_QUANTIFIER`): a pure streak (no total)
        // was measured to multiply the heaviest convergence pin's cost by
        // ~2.3x on top of everything else — a quantifier that keeps
        // mining semantically-fresh-but-unproductive lemmas on a moving
        // model (the set family's compound-closure chase) resets its own
        // streak forever, and a re-checked goal re-pays that hundreds of
        // times.  The total bounds that; the streak still gives a
        // converging quantifier more than the old flat cap of 2.
        if self.checks_of.get(&q.term).copied().unwrap_or(0) >= MAX_CHECKS_PER_QUANTIFIER
            || self.total_checks_of.get(&q.term).copied().unwrap_or(0)
                >= MAX_TOTAL_CHECKS_PER_QUANTIFIER
        {
            self.last_decline = Some("per-quantifier check budget exhausted");
            return ModelCheckOutcome::Declined;
        }
        *self.total_checks_of.entry(q.term).or_insert(0) += 1;

        let signature = completed_model_signature(model);
        // A certification remembered for this exact model is reused without
        // re-paying the nested solve (the dual of `falsified_at`'s veto
        // memory).
        if self
            .certified_at
            .get(&q.term)
            .is_some_and(|sigs| sigs.contains(&signature))
        {
            self.last_decline = None;
            return ModelCheckOutcome::Satisfied;
        }
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
        // need — the base choice merged with the globally accepted
        // revision (see [`ModelChecker::accepted_else`]).  The entry cap
        // counts *chain-relevant* entries — those whose result differs
        // from the function's else — because the ite-chain construction
        // (see `fold_apply`) skips the rest: the enumerative seeder's
        // thousands of default-valued pins must not bury the structural
        // ones.
        let else_preview = choose_else_table(model, manager);
        for (&func, interp) in model.function_interps.iter() {
            let Some(&else_val) = else_preview.get(&func) else {
                continue;
            };
            // The computed constructor entries join the relevance count:
            // they extend the ite chains the budgeted nested check must
            // solve through.
            let computed_count = model.computed_entries.get(&func).map_or(0, |v| v.len());
            let relevant = interp
                .entries
                .iter()
                .filter(|e| value_equal(e.result, else_val, manager) != Some(true))
                .count()
                + computed_count;
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

        // Evaluation-only certification: the completed body folded to the
        // literal `true` — the ite chains and value literals already cover
        // every point of every bound variable's domain, so the completed
        // interpretation satisfies the quantifier outright.  No nested
        // solve is needed, and none is paid for: this branch consumes no
        // check budget (it is evaluation, not search), so a constructor
        // whose table closed the body certifies on every round of a moving
        // model without ever exhausting the per-quantifier caps that bound
        // the *search* (the set-family convergence blocker: the caps
        // silenced certification exactly while the pins kept the model
        // moving).
        if manager
            .get(body_completed)
            .is_some_and(|t| matches!(t.kind, TermKind::True))
        {
            if std::env::var_os("NIXIE_DEBUG_MC").is_some() {
                eprintln!("[mc] certified by evaluation (body' = true)");
            }
            // Refund the per-quantifier total (table mode only — see
            // `mark_productive`): no nested solve ran, and the caps exist
            // to bound *search*, not evaluation.
            if self.table_mode
                && let Some(count) = self.total_checks_of.get_mut(&q.term)
            {
                *count = count.saturating_sub(1);
            }
            self.certified_at.entry(q.term).or_default().push(signature);
            self.checks_of.insert(q.term, 0);
            self.last_decline = None;
            return ModelCheckOutcome::Satisfied;
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
                    self.certified_at.entry(q.term).or_default().push(signature);
                    // A certification is productive: refund the total (see
                    // `mark_productive`; table mode only).
                    if self.table_mode
                        && let Some(count) = self.total_checks_of.get_mut(&q.term)
                    {
                        *count = count.saturating_sub(1);
                    }
                    self.checks_of.insert(q.term, 0);
                    self.last_decline = None;
                    return ModelCheckOutcome::Satisfied;
                }
            }
            result
        } else {
            result
        };
        // NOTE: a bounded per-function else-revision search (Z3's
        // `smt_model_finder` "search, verify, revise" for non-Bool
        // constructors) lived here and was removed: its certifications
        // could rest on *different* one-shot interpretations for
        // different quantifiers (q1 needing `union`'s else to be `b`, q2
        // needing `a` — no single model of the conjunction exhibited), it
        // demonstrated no win anywhere (set16's violating points are
        // entry-shaped, not default-shaped), and making it globally
        // consistent (one accepted revision merged into every later
        // check) quadrupled the convergence pins' cost by reshaping every
        // subsequent aux goal.  The entry-table search that would
        // actually close the set family is recorded as its own project in
        // docs/studies/2026-09-14-uflra-handoff-executed.md.
        if std::env::var_os("NIXIE_DEBUG_MC").is_some() {
            eprintln!("[mc] aux verdict q={:?}: {:?}", q.term, result);
        }

        match result {
            Ok(SolverResult::Unsat) => {
                // A certification for this exact model: remembered so later
                // rounds against the same completed model reuse it, and a
                // productive outcome (resets the wasted-solve streak — and
                // refunds the per-quantifier total; see `mark_productive`).
                self.certified_at.entry(q.term).or_default().push(signature);
                if self.table_mode
                    && let Some(count) = self.total_checks_of.get_mut(&q.term)
                {
                    *count = count.saturating_sub(1);
                }
                self.checks_of.insert(q.term, 0);
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
                // sample, not a domain).  A constructor argument axis of a
                // defining axiom takes its *semantic* domain instead: the
                // universe with compounds collapsed through the computed
                // tables (`union(b,b)` and `b` are one point), so the
                // odometer stops re-mining falsifiers the table already
                // closed.
                let sets: Vec<Vec<TermId>> = skolem_terms
                    .iter()
                    .enumerate()
                    .map(|(i, &(_, sort, _))| {
                        if let Some(domain) = model.semantic_domains.get(&(q.term, i)) {
                            return domain.clone();
                        }
                        // Table mode: every axis of every quantifier
                        // ranges over the frozen table domain (see the
                        // seeder's twin note) — the raw universe grows
                        // with every witness the ground solver mints
                        // (nested Skolem applications among them), and
                        // mining the fresh points re-moves the model
                        // every round.
                        if !model.constructor_sources.is_empty()
                            && let Some(domain) = model.table_domain(sort, manager)
                        {
                            return domain;
                        }
                        let finite_universe = manager
                            .sorts
                            .get(sort)
                            .is_some_and(|s| matches!(s.kind, SortKind::Uninterpreted(_)))
                            .then(|| model.ground_universe(sort, manager))
                            .flatten()
                            .filter(|u| !u.is_empty() && u.len() <= MAX_UNIVERSE_FOR_RESTRICTION)
                            // One representative per *model value*: two
                            // elements the model assigns the same value are
                            // the same domain point, and a falsifier at one
                            // is a falsifier at the other — mining both
                            // emits a semantically-redundant lemma that
                            // keeps the rounds "productive" while the model
                            // never moves (the productive-spin shape; see
                            // `build_small_domains` for the enumerative
                            // twin of this normalization).
                            .map(|u| {
                                let mut seen: FxHashSet<TermId> = FxHashSet::default();
                                u.into_iter()
                                    .filter(|e| {
                                        let v = model.assignments.get(e).copied().unwrap_or(*e);
                                        seen.insert(v)
                                    })
                                    .collect::<Vec<_>>()
                            });
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
                let mut mined: Vec<MinedFalsifier> = Vec::new();
                let mut odometer = vec![0usize; sets.len()];
                let mut tried = 0usize;
                'combo: loop {
                    if tried >= MAX_COMBO_PRODUCT || mined.len() >= MAX_CEX_PER_CHECK {
                        break;
                    }
                    tried += 1;
                    // Evaluate the completed body under this combination,
                    // recording the ground commitments the evaluation leans
                    // on (for the blocking clause; see `run_recorded`).
                    let mut subst: FxHashMap<TermId, TermId> = FxHashMap::default();
                    for (i, &(name, sort, _)) in skolem_terms.iter().enumerate() {
                        let value = sets[i][odometer[i]];
                        let name_str = manager.resolve_str(name).to_string();
                        subst.insert(manager.mk_var(&name_str, sort), value);
                    }
                    // The recording walk runs on the *raw* substituted
                    // body, never the completed translation: the
                    // completed body's syntax already bakes the
                    // completion's choices (macro unfoldings, ite-chain
                    // shapes, else leaves) in places the walk cannot see,
                    // so a "fully pinned" verdict over it counts choices
                    // as pins — and a blocking clause built from it
                    // refutes satisfiable goals (the 2026-09-15
                    // re-derivation of the original removal's false-
                    // `unsat`: quant_fuzz seeds 41-46, six disagreements).
                    // On the raw body every completion choice the walk
                    // consumes passes through `fold_apply`'s macro/computed/
                    // else arms, which flag it — the transfer argument's
                    // recording is then complete.
                    let substituted = manager.substitute(q.body, &subst);
                    // The mining evaluation's symbolic set is the
                    // tracked bound-variable NAMES, not the empty set:
                    // the substitution has replaced every legitimate
                    // bound variable, so nothing legitimate turns
                    // symbolic — but an *artifact* variable (an encoder
                    // binder constant that leaked through a completion
                    // entry chain) does, which declines the
                    // universe-distinctness fold for it instead of
                    // fabricating `(= artifact c_i) -> false` (the
                    // 2026-09-14 false-`sat` mechanism).
                    let artifact_names = &model.bound_var_names;
                    let (evaluated, commitments, free_choice, _consulted) =
                        CompletionEval::run_recorded(
                            substituted,
                            model,
                            artifact_names,
                            &else_table,
                            manager,
                        );
                    if evaluated.is_ok_and(|t| t == false_term) {
                        let mut falsifying: FxHashMap<Spur, TermId> = FxHashMap::default();
                        for (i, &(name, _, _)) in skolem_terms.iter().enumerate() {
                            let raw = sets[i][odometer[i]];
                            let chosen = value_to_term.get(&raw).copied().unwrap_or(raw);
                            falsifying.insert(name, chosen);
                        }
                        mined.push(MinedFalsifier {
                            substitution: falsifying,
                            commitments,
                            fully_pinned: !free_choice,
                        });
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
                    // A wasted solve (no minable falsifier at all — the
                    // liar shape): counts toward the streak unless the
                    // caller's veto path learns something fresh.
                    *self.checks_of.entry(q.term).or_insert(0) += 1;
                    return ModelCheckOutcome::Counterexample {
                        falsifiers: Vec::new(),
                    };
                }
                self.last_decline = None;
                if std::env::var_os("NIXIE_DEBUG_MC").is_some() {
                    let printer = nixie_core::smtlib::Printer::new(manager);
                    for falsifier in &mined {
                        let subs: Vec<String> = falsifier
                            .substitution
                            .iter()
                            .map(|(k, v)| {
                                format!("{} := {}", manager.resolve_str(*k), printer.print_term(*v))
                            })
                            .collect();
                        eprintln!(
                            "[mc] cex bindings: {} [pinned={}, commitments={}]",
                            subs.join(", "),
                            falsifier.fully_pinned,
                            falsifier.commitments.len()
                        );
                    }
                }
                // The solve ran and did not certify: a wasted solve unless
                // the caller mines a fresh instantiation from these
                // falsifiers (`mark_productive` then resets the streak).
                *self.checks_of.entry(q.term).or_insert(0) += 1;
                ModelCheckOutcome::Counterexample { falsifiers: mined }
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
        aux.debug_tag = Some("-aux");
        aux.set_logic(logic.unwrap_or("ALL"));
        // The aux solver exists to decide one goal: `not body'[sk]` —
        // with the bounded-quantifier expansion this goal is
        // quantifier-free, and where a binder survived (a sampled sort,
        // an over-cap product) the aux's *own* MBQI loop adds nothing
        // the verdict needs (an unsat under the wrapper-dodge reading is
        // unsat under the true reading too; a sat verdict yields the
        // falsifier the mining verifies).  What it did add was budget
        // churn: the nested rounds' conflicts are charged to THIS
        // checker's global budget through `aux.stats()`, and a handful
        // of main-level checks whose aux went digging burned the whole
        // 50k budget from the inside — every later main-level check then
        // declined silently on the global gate (the set family's
        // cap-starvation stall).
        // Table mode only (see below): on goals *with* tables the aux's
        // own MBQI added nothing but budget churn; on goals without
        // them it occasionally contributed the refutation the outer
        // loop could not reach alone (wisas/xs_8_13 lost its `unsat`
        // when this was unconditional — the nested search inside an aux
        // check found it).
        if !model.constructor_sources.is_empty() {
            aux.mbqi.set_max_rounds(0);
        }
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
            // A tabled sort's completed structure has its own (frozen,
            // semantic) domain — the restriction confines the Skolems to
            // exactly that, the points the interpretation is defined over.
            let finite_universe = manager
                .sorts
                .get(sort)
                .is_some_and(|s| matches!(s.kind, SortKind::Uninterpreted(_)))
                .then(|| model.table_domain(sort, manager))
                .flatten();
            if let Some(universe) = finite_universe
                && !universe.is_empty()
                && universe.len() <= MAX_UNIVERSE_FOR_RESTRICTION
            {
                let restriction: Vec<TermId> =
                    universe.iter().map(|&u| manager.mk_eq(sk, u)).collect();
                aux.assert(manager.mk_or(restriction), manager);
                // The domain elements are pairwise distinct *by
                // construction* — the universe is the set of the model's
                // distinguished values — and without telling the aux, a
                // Skolem restricted to `{a, b}` may satisfy its restriction
                // by *merging* `a` and `b` (both disjuncts true under the
                // merge): a degenerate point that is not an element of the
                // structure, where the ite-chain branch of `(b, a)` fires
                // with `member(x, s1)` and `member(x, s2)` collapsed to the
                // same term — `p ∧ ¬p` — and every witness axiom falsifies
                // at it.  Z3's model values are distinct by the same
                // construction; this is that, told to the aux.
                let distinct = manager.intern_term(
                    TermKind::Distinct(universe.iter().copied().collect()),
                    manager.sorts.bool_sort,
                );
                aux.assert(distinct, manager);
            }
        }

        // not body[sk]  — refute the completed interpretation.
        let substitution = skolem_var_map(skolem_terms, manager);
        let skolemized = manager.substitute(body, &substitution);
        let goal = manager.mk_not(skolemized);
        aux.assert(goal, manager);

        // The goal's Set-sorted ite chains are Tseitin-abstracted into
        // fresh `__nixie_ite_*` variables by the encoder, and a *nested*
        // chain's condition mentions them (`(= sk __nixie_ite_N)`) — a
        // condition the Skolem restriction does not decide, so the aux
        // could set the abstraction freely and falsify through the hole:
        // every chain value IS a domain element (an entry result or the
        // else — both drawn from the structure), so confining the ite
        // variables to the same domain is exactly the chain's semantics,
        // not an extra assumption.
        {
            let ite_vars: Vec<TermId> = aux.ite_result_terms.iter().copied().collect();
            for v in ite_vars {
                let Some(node) = manager.get(v) else { continue };
                let uninterpreted = manager
                    .sorts
                    .get(node.sort)
                    .is_some_and(|s| matches!(s.kind, SortKind::Uninterpreted(_)));
                if !uninterpreted {
                    continue;
                }
                let Some(domain) = model.table_domain(node.sort, manager) else {
                    continue;
                };
                if domain.is_empty() || domain.len() > MAX_UNIVERSE_FOR_RESTRICTION {
                    continue;
                }
                let restriction: Vec<TermId> =
                    domain.iter().map(|&u| manager.mk_eq(v, u)).collect();
                aux.assert(manager.mk_or(restriction), manager);
            }
        }

        self.checks_performed += 1;
        let conflicts_before = aux.stats().conflicts;
        let limits = ResourceLimits::new()
            .with_max_conflicts(AUX_CONFLICT_LIMIT)
            .with_max_decisions(AUX_DECISION_LIMIT);
        let verdict = aux.check_with_limits(manager, &limits);
        // Charge the conflicts actually spent, not the per-check cap: the
        // global budget exists to bound real work, and a nested solve that
        // decides its goal in a handful of conflicts must not burn a full
        // cap's worth (the broadened escalation runs several checks per
        // round; cap-charging exhausted the global budget after 12 checks
        // and silenced the certification the loop needs to converge).
        let spent = aux
            .stats()
            .conflicts
            .saturating_sub(conflicts_before)
            .max(1);
        self.conflicts_spent = self.conflicts_spent.saturating_add(spent);
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
                    // Bucket by the value's OWN sort, never the argument
                    // position's declared sort: the two coincide on a
                    // well-typed entry, and an ill-typed one (a harvested
                    // artifact) must not seed this sort's instantiation
                    // set with a foreign-sorted value — that is the
                    // ill-typed-instantiation vector (`?s1 := u!4` with
                    // `u!4` an Elem term in a Set position).
                    let norm = model.assignments.get(&arg).copied().unwrap_or(arg);
                    let value_sort = manager.get(norm).map_or(domain_sort, |nd| nd.sort);
                    value_of(value_sort, norm, arg, &mut sorts);
                }
                if !mentions_bound(entry.result) {
                    let result_sort = manager.get(entry.result).map_or(interp.range, |nd| nd.sort);
                    value_of(result_sort, entry.result, entry.result, &mut sorts);
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
            // A cross-sorted assignment (a harvested artifact) is not a
            // value of this sort — skip it rather than seed the
            // instantiation set with a foreign-sorted term.
            if manager.get(value).is_some_and(|v| v.sort != node.sort) {
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
/// The bounded-quantifier expansion's substitution tuples: one per point
/// of the product of the bound variables' finite domains, or `None` when
/// any bound variable's sort is not finitely restrictable (not an
/// uninterpreted sort, no non-empty domain, over the restriction bound, or
/// the product over the expansion cap) — the binder then stays symbolic
/// and the nested check decides it, exactly as before.
///
/// The domain source is [`CompletedModel::table_domain`] — the *same*
/// source the nested check's Skolem restriction reads — so the expansion
/// and the restriction always agree on what the binder ranges over.
fn quantifier_tuples(
    vars: &SmallVec<[(Spur, SortId); 2]>,
    model: &CompletedModel,
    manager: &mut TermManager,
) -> Option<Vec<FxHashMap<TermId, TermId>>> {
    /// Cap on the expanded product per binder (matches the hint
    /// machinery's bounded-quantifier evaluation).
    const MAX_EXPANSION_PRODUCT: usize = 64;
    let mut domains: Vec<Vec<TermId>> = Vec::with_capacity(vars.len());
    for &(_, sort) in vars {
        let uninterpreted = manager
            .sorts
            .get(sort)
            .is_some_and(|s| matches!(s.kind, SortKind::Uninterpreted(_)));
        if !uninterpreted {
            return None;
        }
        let domain = model.table_domain(sort, manager)?;
        if domain.is_empty() || domain.len() > MAX_UNIVERSE_FOR_RESTRICTION {
            return None;
        }
        domains.push(domain);
    }
    let product: usize = domains.iter().map(|d| d.len()).product();
    if product > MAX_EXPANSION_PRODUCT {
        return None;
    }
    let mut tuples: Vec<FxHashMap<TermId, TermId>> = Vec::with_capacity(product);
    let mut odometer = vec![0usize; vars.len()];
    loop {
        let mut subst: FxHashMap<TermId, TermId> = FxHashMap::default();
        for (i, &(name, sort)) in vars.iter().enumerate() {
            let name_str = manager.resolve_str(name).to_string();
            let var = manager.mk_var(&name_str, sort);
            subst.insert(var, domains[i][odometer[i]]);
        }
        tuples.push(subst);
        if vars.is_empty() {
            break;
        }
        let mut carry = true;
        for (i, idx) in odometer.iter_mut().enumerate() {
            if carry {
                *idx += 1;
                if *idx >= domains[i].len() {
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
    Some(tuples)
}

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
pub(crate) fn choose_else_table(
    model: &CompletedModel,
    manager: &mut TermManager,
) -> FxHashMap<Spur, TermId> {
    let mut table: FxHashMap<Spur, TermId> = FxHashMap::default();
    for (&func, interp) in &model.function_interps {
        if let Some(else_val) = choose_else(interp, model, manager) {
            table.insert(func, else_val);
        }
    }
    table
}

/// Evaluate a *ground* term under the completed model (entries, computed
/// constructor entries, macros, else) with no symbolic names: the
/// constructor-table search's row/target evaluator.  Declines (like
/// [`CompletionEval::run`]) when the term does not fold.
pub(crate) fn eval_completed_ground(
    term: TermId,
    model: &CompletedModel,
    else_table: &FxHashMap<Spur, TermId>,
    manager: &mut TermManager,
) -> Result<TermId, &'static str> {
    let bound: FxHashSet<Spur> = FxHashSet::default();
    CompletionEval::run(term, model, &bound, else_table, manager)
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
    // The computed constructor tables and the semantic domains are part
    // of the interpretation: a certification remembered for a signature
    // must not survive a table change.
    model.computed_entries.len().hash(&mut hasher);
    for entries in model.computed_entries.values() {
        entries.len().hash(&mut hasher);
        for entry in entries {
            for &a in &entry.args {
                a.0.hash(&mut hasher);
            }
            entry.result.0.hash(&mut hasher);
        }
    }
    model.semantic_domains.len().hash(&mut hasher);
    for domain in model.semantic_domains.values() {
        domain.len().hash(&mut hasher);
        for &e in domain {
            e.0.hash(&mut hasher);
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
        Some(SortKind::Uninterpreted(_)) => model
            .ground_universe(sort, manager)
            .and_then(|u| u.first().copied()),
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
pub(crate) fn push_children(kind: &TermKind, out: &mut ChildList) {
    match kind {
        TermKind::Forall { body, .. } | TermKind::Exists { body, .. } => out.push(*body),
        TermKind::Let { .. } | TermKind::Match { .. } => {}
        TermKind::Not(a) => out.push(*a),
        // Finite sets: ordinary children. Whether MBQI can *rebuild* them is
        // decided separately, in `rebuild`.
        TermKind::SetSingleton(a)
        | TermKind::SetCard(a)
        | TermKind::SetComplement(a)
        | TermKind::SetChoose(a)
        | TermKind::SetRelTranspose(a)
        | TermKind::SetRelIden(a)
        | TermKind::BagCard(a)
        | TermKind::BagSetof(a)
        | TermKind::BagChoose(a)
        | TermKind::BagMap { bag: a, .. }
        | TermKind::BagFilter { bag: a, .. } => out.push(*a),
        // A fold's children in positional order: the initial accumulator,
        // then the domain bag (the order `rebuild_with` indexes them by).
        TermKind::BagFold { init, bag, .. } => {
            out.push(*init);
            out.push(*bag);
        }
        TermKind::SetUnion(a, b)
        | TermKind::SetInter(a, b)
        | TermKind::SetMinus(a, b)
        | TermKind::SetMember(a, b)
        | TermKind::SetRelJoin(a, b)
        | TermKind::SetRelProduct(a, b)
        | TermKind::SetSubset(a, b)
        | TermKind::BagMake(a, b)
        | TermKind::BagUnionMax(a, b)
        | TermKind::BagUnionDisjoint(a, b)
        | TermKind::BagInterMin(a, b)
        | TermKind::BagDifferenceSubtract(a, b)
        | TermKind::BagDifferenceRemove(a, b)
        | TermKind::BagMember(a, b)
        | TermKind::BagSubbag(a, b)
        | TermKind::BagCount(a, b) => {
            out.push(*a);
            out.push(*b);
        }
        TermKind::SetEmpty(_) | TermKind::SetUniv(_) | TermKind::BagEmpty(_) => {}
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
    /// Whether this evaluation records its supporting commitments and free
    /// choices (see [`CompletionEval::run_recorded`]).
    recording: bool,
    /// The ground atoms whose completed values the evaluation consumed:
    /// `(atom, value)` with `atom` Bool-sorted and `value` its truth value.
    commitments: Vec<(TermId, TermId)>,
    /// Whether any value was resolved through a *free* completion choice
    /// (an `else` fallthrough, a macro expansion, a sort default, a
    /// universe fold) rather than a ground-model fact.
    free_choice: bool,
    /// Functions whose `else` default this evaluation consulted (the
    /// revision targets for the bounded else-search — Z3's
    /// `smt_model_finder` "search, verify, revise": a falsified body whose
    /// evaluation leaned on a function's default is repaired by revising
    /// *that* default, not by pinning every compound point).
    else_consulted: FxHashSet<Spur>,
}

/// The evidence one recorded evaluation collects (see
/// [`CompletionEval::run_recorded`]): the result, the supporting
/// commitments, whether a free completion choice was consumed, and which
/// functions' `else` defaults were consulted.
type RecordedRun = (
    Result<TermId, &'static str>,
    Vec<(TermId, TermId)>,
    bool,
    FxHashSet<Spur>,
);

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
            recording: false,
            commitments: Vec::new(),
            free_choice: false,
            else_consulted: FxHashSet::default(),
        };
        eval.eval(root, manager)
    }

    /// Evaluate `root` while recording the evaluation's supporting
    /// commitments and free choices.  The caller uses the evidence to build
    /// a Z3-style blocking clause (`add_blocking_clause`): when a falsifier
    /// is `fully_pinned` (no free choice consumed), the falsification is a
    /// function of the recorded commitments alone, so excluding that value
    /// arrangement from the next candidate model loses no solution.
    fn run_recorded(
        root: TermId,
        model: &'a CompletedModel,
        bound: &'a FxHashSet<Spur>,
        else_table: &'a FxHashMap<Spur, TermId>,
        manager: &mut TermManager,
    ) -> RecordedRun {
        let mut eval = Self {
            model,
            bound,
            else_table,
            cache: FxHashMap::default(),
            symbolic: FxHashMap::default(),
            nodes_visited: 0,
            macro_depth: 0,
            recording: true,
            commitments: Vec::new(),
            free_choice: false,
            else_consulted: FxHashSet::default(),
        };
        let result = eval.eval(root, manager);
        let evidence = core::mem::take(&mut eval.commitments);
        let consulted = core::mem::take(&mut eval.else_consulted);
        (result, evidence, eval.free_choice, consulted)
    }

    /// The functions whose `else` default the recorded evaluation
    /// consulted (see [`CompletionEval::else_consulted`]).
    fn consulted_else_defaults(&self) -> Vec<Spur> {
        self.else_consulted.iter().copied().collect()
    }

    /// Record a commitment: the ground atom `term` resolved to `value`.
    /// Bool-sorted terms commit directly; other sorts commit through the
    /// equality atom `term = value` (the caller drops clauses whose atoms
    /// the ground solver never internalized).
    fn record_commitment(&mut self, term: TermId, value: TermId, manager: &mut TermManager) {
        if !self.recording {
            return;
        }
        let is_bool = manager
            .get(term)
            .is_some_and(|n| n.sort == manager.sorts.bool_sort);
        if is_bool {
            self.commitments.push((term, value));
        } else {
            let atom = manager.mk_eq(term, value);
            let truth = manager.mk_true();
            self.commitments.push((atom, truth));
        }
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
            /// A bounded-quantifier expansion in flight (see the binder arm
            /// of `Enter`): the tuples are precomputed substitutions over
            /// the bound variables' finite domains, `next` indexes the one
            /// whose substituted body was most recently pushed as an
            /// `Enter`, and `done` collects their evaluated truths.
            Quant {
                node: TermId,
                body: TermId,
                tuples: Vec<FxHashMap<TermId, TermId>>,
                next: usize,
                done: Vec<TermId>,
                is_forall: bool,
            },
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
                    //
                    // A *binder* node is never a ground-model fact either:
                    // its assignment-table row is the SAT core's wrapper
                    // Boolean for the quantified subformula — a commitment
                    // the search chose to dodge the subformula's
                    // consequences, not the subformula's truth value.
                    // Reading it fabricated `(forall z. true) -> false`
                    // and certified `(=> (forall z. true) (P x y))`
                    // vacuously (the strengthened quant_fuzz false-`sat`).
                    let is_binder =
                        matches!(node.kind, TermKind::Forall { .. } | TermKind::Exists { .. });
                    if !is_binder && !self.is_symbolic(term, manager) {
                        if let Some(&value) = self.model.assignments.get(&term) {
                            self.record_commitment(term, value, manager);
                            self.cache.insert(term, value);
                            values.push(value);
                            continue;
                        }
                    }
                    let kind_pre = node.kind.clone();
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
                        TermKind::Forall { vars, body, .. }
                        | TermKind::Exists { vars, body, .. } => {
                            // Bounded-quantifier expansion (Z3's model
                            // evaluator does exactly this over its finite
                            // model universes): when every bound variable
                            // ranges over a finite *restrictable* domain —
                            // the very domains the nested check's Skolem
                            // restriction confines that variable to — the
                            // binder is replaced by the pointwise fold
                            // (`forall x. phi` -> `and(phi[d])`), making
                            // the completed body quantifier-free.  This is
                            // not an approximation: the restricted nested
                            // solve decides exactly the expanded reading,
                            // and doing it at completion time turns a
                            // nested full-solve (whose own quantifier loop
                            // burns budgets per check — the set family's
                            // certification stall) into a plain chain
                            // solve.  Binders over sampled/infinite sorts
                            // (Int, Real, ...) stay symbolic, as before.
                            let is_forall = matches!(kind_pre, TermKind::Forall { .. });
                            match quantifier_tuples(&vars, self.model, manager) {
                                Some(tuples) => {
                                    if tuples.is_empty() {
                                        // An empty domain cannot happen for
                                        // a restrictable sort (the aux
                                        // restriction skips those too); if
                                        // it somehow does, stay symbolic.
                                        stack.push(Frame::Fold(term));
                                        stack.push(Frame::Enter(body));
                                        continue;
                                    }
                                    let first = manager.substitute(body, &tuples[0]);
                                    stack.push(Frame::Quant {
                                        node: term,
                                        body,
                                        tuples,
                                        next: 0,
                                        done: Vec::new(),
                                        is_forall,
                                    });
                                    stack.push(Frame::Enter(first));
                                }
                                None => {
                                    stack.push(Frame::Fold(term));
                                    stack.push(Frame::Enter(body));
                                }
                            }
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
                Frame::Quant {
                    node,
                    body,
                    tuples,
                    next,
                    mut done,
                    is_forall,
                } => {
                    // The most recent value is this tuple's truth.
                    let Some(value) = values.pop() else {
                        return Err("quantifier expansion lost a value");
                    };
                    // The expansion's *domain* is a completion choice:
                    // which elements exist is the interpretation's own
                    // decision (the frozen table domain), not a ground
                    // fact.  A falsifier whose falsity needed the
                    // expansion — `not subset => exists x. ...` with no
                    // witness *among the chosen elements* — is not a
                    // function of its recorded commitments alone: a model
                    // agreeing on every pin but carrying the missing
                    // element satisfies the quantifier.  The blocking
                    // clause built from such a falsifier blocks an
                    // arrangement that includes asserted facts
                    // (`subset(b,a) = false`) and refutes satisfiable
                    // goals (found live on set16: the pre-thaw falsifier
                    // at `(b, a)`, fully pinned under the old flag).
                    if self.recording {
                        self.free_choice = true;
                    }
                    let decided = if is_forall {
                        manager
                            .get(value)
                            .is_some_and(|t| matches!(t.kind, TermKind::False))
                    } else {
                        manager
                            .get(value)
                            .is_some_and(|t| matches!(t.kind, TermKind::True))
                    };
                    done.push(value);
                    let result = if decided {
                        // Short-circuit: `forall` found a false point /
                        // `exists` found a witness — no further tuple can
                        // change the fold.
                        value
                    } else if next + 1 < tuples.len() {
                        let upcoming = manager.substitute(body, &tuples[next + 1]);
                        stack.push(Frame::Quant {
                            node,
                            body,
                            tuples,
                            next: next + 1,
                            done,
                            is_forall,
                        });
                        stack.push(Frame::Enter(upcoming));
                        continue;
                    } else {
                        // Fold the collected truths.
                        if is_forall {
                            if done.iter().all(|&t| {
                                manager
                                    .get(t)
                                    .is_some_and(|n| matches!(n.kind, TermKind::True))
                            }) {
                                manager.mk_true()
                            } else {
                                manager.mk_and(done.iter().copied())
                            }
                        } else {
                            manager.mk_or(done.iter().copied())
                        }
                    };
                    self.cache.insert(node, result);
                    values.push(result);
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
                            // A pointwise-constant body makes the binder that
                            // constant (`forall x. true -> true`, dually to the
                            // `Exists` arm below): SMT-LIB sorts are all
                            // non-empty, so `forall x. false -> false` and
                            // `exists x. true -> true` fold exactly as well.
                            // Leaving a constant-bodied `forall` symbolic kept
                            // A3's completed body `(forall x. true) => false`
                            // opaque to the aux solver's own (budgeted)
                            // quantifier loop instead of the plain `false` it
                            // pointwise is.
                            if manager
                                .get(folded)
                                .is_some_and(|t| matches!(t.kind, TermKind::True | TermKind::False))
                            {
                                folded
                            } else {
                                manager.intern_term(
                                    TermKind::Forall {
                                        vars: vars.clone(),
                                        body: folded,
                                        patterns: patterns.clone(),
                                    },
                                    node.sort,
                                )
                            }
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
                                        // *ground* universe representatives
                                        // of the same sort are unequal by
                                        // construction (the universe is a
                                        // set of pairwise-distinct
                                        // elements).  Without this fold the
                                        // ite-chain conditions `(= z a)` of
                                        // a mined substitution stay symbolic
                                        // and the falsifier the aux check
                                        // found at `(z,z)` is never mined
                                        // (the set-family diagonal stall).
                                        //
                                        // Groundness of BOTH operands is
                                        // load-bearing: the universe
                                        // contains bound-variable artifact
                                        // terms (entry args harvested by
                                        // `collect_universes_from_model`),
                                        // and folding symbolic operands
                                        // fabricates `?s1 != ?s2` — with
                                        // it both a fake falsifier and, on
                                        // `(distinct s1 s2) \/ psi`-shaped
                                        // bodies, a fabricated pointwise
                                        // `true` the completion does not
                                        // justify (a false-`Satisfied`).
                                        // The fold is also a *universe*
                                        // fact, not a ground-model pin, so
                                        // it counts as a free choice for
                                        // blocking-clause purposes.
                                        let a_symbolic = self.is_symbolic(a, manager);
                                        let b_symbolic = self.is_symbolic(b, manager);
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
                                            (!a_symbolic && !b_symbolic && a_in && b_in)
                                                .then_some(false)
                                        })();
                                        if self.recording && matches!(verdict, Some(false)) {
                                            self.free_choice = true;
                                        }
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
                // A macro read is a definitional-axiom reduction, not a
                // ground-model fact: for blocking purposes it is a free
                // choice (the defining axiom itself may be the quantifier
                // under check, and the reduction consults other functions'
                // entries at symbolic points).
                if self.recording {
                    self.free_choice = true;
                }
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
                        // An entry hit is a ground-model fact (the table is
                        // harvested from the ground solver's pinned
                        // applications): commit the atom `f(args) = result` —
                        // and, for the blocking clause's transfer argument,
                        // every assignment normalization the match leaned on
                        // (`entry_arg` read through its model value): a
                        // target model that keeps `entry_arg` and its value
                        // distinct would have matched a different entry, and
                        // the falsity would not transfer.
                        if self.recording {
                            let args: ChildList = evaluated_args.iter().copied().collect();
                            let app = manager.intern_term(TermKind::Apply { func, args }, sort);
                            let atom = manager.mk_eq(app, entry.result);
                            let truth = manager.mk_true();
                            self.commitments.push((atom, truth));
                            for &entry_arg in &entry.args {
                                if let Some(&norm) = self.model.assignments.get(&entry_arg)
                                    && norm != entry_arg
                                {
                                    let eq_atom = manager.mk_eq(entry_arg, norm);
                                    self.commitments.push((eq_atom, truth));
                                }
                            }
                        }
                        return Ok(entry.result);
                    }
                }
            }
            // Computed constructor entries (see `constructor_tables`):
            // consulted after the ground pins — the table's whole design
            // is "never override a pin" — and before the `else`.  A hit is
            // an interpretation *choice*, not a ground fact.
            if let Some(computed) = self.model.computed_entries.get(&func) {
                for entry in computed {
                    if args_match(entry, evaluated_args, self.model, manager) {
                        if self.recording {
                            self.free_choice = true;
                        }
                        return Ok(entry.result);
                    }
                }
            }
            if let Some(&else_val) = self.else_table.get(&func) {
                // An `else` fallthrough is a completion choice, not a
                // ground-model pin.
                if self.recording {
                    self.free_choice = true;
                    self.else_consulted.insert(func);
                }
                return Ok(else_val);
            }
            // No interpretation and no else: keep the application as a free
            // ground term (unconstrained by the model; the nested solver
            // sees it as itself).
            if self.recording {
                self.free_choice = true;
            }
            let args: ChildList = evaluated_args.iter().copied().collect();
            return Ok(manager.intern_term(TermKind::Apply { func, args }, sort));
        }

        // Symbolic argument: the entry table as an ite chain, else leaf.
        if self.recording {
            // The chain encodes entries under symbolic conditions — not a
            // ground pin the blocking clause can lean on.
            self.free_choice = true;
            self.else_consulted.insert(func);
        }
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
        // The chain covers the computed constructor entries too (see
        // `constructor_tables`): ground entries shadow computed ones — the
        // chained iteration processes the computed entries first so the
        // ground pins nest outermost and win, mirroring the concrete
        // path's priority.
        let computed: &[FunctionEntry] = self
            .model
            .computed_entries
            .get(&func)
            .map_or(&[], |v| v.as_slice());
        let ground: &[FunctionEntry] = interp.map_or(&[], |i| i.entries.as_slice());
        let mut acc = else_leaf;
        for entry in ground.iter().chain(computed.iter()).rev() {
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
                // Semantic normalization: a compound entry argument (a
                // minted `union(a,a)`-keyed pin from the search era)
                // denotes the same domain point as its semantic value —
                // the completed structure identifies them — so the chain
                // must compare the Skolem against the *representative*,
                // not the compound.  Without this, the nested check —
                // which may legitimately merge the Skolem with the
                // compound — routes the chain through the stale
                // compound-keyed entries that disagree with the
                // domain-keyed ones.
                let entry_norm = self.model.semantic_value_of(entry_norm, manager);
                // The normalization chain is a ground-model consult the
                // syntax bakes in: record it so a blocking clause over
                // this evaluation's commitments is not stronger than what
                // the evaluation actually leaned on (see the concrete
                // path's twin note).
                if self.recording && entry_norm != entry_arg {
                    let truth = manager.mk_true();
                    let eq_atom = manager.mk_eq(entry_arg, entry_norm);
                    self.commitments.push((eq_atom, truth));
                }
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
            // `p => p` collapses to `true` (and a decided side
            // short-circuits): without the collapse, an antecedent whose
            // atoms fell through to the else — leaving hash-consed
            // identical symbolic terms like `(member u!0 a)` — stays a
            // non-constant and-chain of trivial implications, the walk
            // reports "not false" where every solver reads `true`, and
            // the falsifier the aux found at that point is never mined
            // (the walk-vs-aux divergence of the set family's axiom-3
            // diagonal).
            if a == b {
                manager.mk_true()
            } else {
                let a_true = manager
                    .get(a)
                    .is_some_and(|t| matches!(t.kind, TermKind::True));
                let b_true = manager
                    .get(b)
                    .is_some_and(|t| matches!(t.kind, TermKind::True));
                let a_false = manager
                    .get(a)
                    .is_some_and(|t| matches!(t.kind, TermKind::False));
                if b_true || a_false {
                    manager.mk_true()
                } else if a_true {
                    b
                } else {
                    manager.mk_implies(a, b)
                }
            }
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
        TermKind::SetUniv(sort) => manager.mk_set_univ_at(*sort),
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
        TermKind::SetComplement(_) => manager.mk_set_complement(one(0)?),
        TermKind::SetChoose(..) => {
            return Err("set.choose has no theory to evaluate it");
        }
        TermKind::SetRelJoin(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_rel_join(a, b)
        }
        TermKind::SetRelProduct(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_rel_product(a, b)
        }
        TermKind::SetRelTranspose(..) => manager.mk_rel_transpose(one(0)?),
        TermKind::SetRelIden(..) => manager.mk_rel_iden(one(0)?),
        // Finite bags rebuild structurally; the count/member/subbag truth
        // needs the bag theory and is declined, exactly as the set
        // predicates are.
        TermKind::BagEmpty(sort) => manager.mk_bag_empty_at(*sort),
        TermKind::BagMake(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bag_make(a, b)
        }
        TermKind::BagUnionMax(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bag_union_max(a, b)
        }
        TermKind::BagUnionDisjoint(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bag_union_disjoint(a, b)
        }
        TermKind::BagInterMin(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bag_inter_min(a, b)
        }
        TermKind::BagDifferenceSubtract(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bag_difference_subtract(a, b)
        }
        TermKind::BagDifferenceRemove(..) => {
            let (a, b) = two_at(0)?;
            manager.mk_bag_difference_remove(a, b)
        }
        TermKind::BagMember(..)
        | TermKind::BagSubbag(..)
        | TermKind::BagCount(_, _)
        | TermKind::BagCard(_) => {
            return Err("bag predicate has no theory to evaluate it");
        }
        TermKind::BagSetof(..) => manager.mk_bag_setof(one(0)?),
        TermKind::BagChoose(..) => {
            return Err("bag.choose has no theory to evaluate it");
        }
        TermKind::BagMap { .. } | TermKind::BagFilter { .. } => {
            return Err("bag.map/bag.filter have no theory to evaluate them");
        }
        TermKind::BagFold { func, .. } => {
            // Rebuild the fold node over the evaluated children; the
            // function symbol is a payload, rebuilt from its interned
            // name. MBQI's candidate evaluation of a fold rests on the
            // model's own bag/fun values like any other compound — no
            // separate evaluation is attempted here.
            let (i, b) = two_at(0)?;
            let name = manager.resolve_str(*func).to_string();
            manager.mk_bag_fold(&name, i, b)
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
pub(crate) fn args_match(
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
