//! Bounded array-model completion with independent validity certificates.
//!
//! Proposals are constant arrays or finite store chains over a default. A
//! proposal is installed only after its substituted original assertions are
//! certified: universals by an unsatisfiable negated body, existentials by
//! verified witnesses, and the remaining Boolean context by a validity query.
//! A satisfiable or unknown certificate query never licenses `Sat`.
//!
//! Read-only references: upstream 0.3.4 array_completion_certify and Z3's
//! model/model_evaluator.cpp. Published-model formatting is checked separately.

use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::interner::Spur;
use nixie_core::reserved::reserved_name;
use nixie_core::sort::{SortId, SortKind};
use rustc_hash::{FxHashMap, FxHashSet};

use super::model_eval::EvalOutcome;
use super::types::Model;
use super::{EvalVal, Solver, SolverResult};
use nixie_core::reserved::CONST_ARRAY_FUNC;

mod array_values;
mod declined;
mod groups;
mod infinite;
mod pinned;
mod polarity;
mod split;
#[cfg(test)]
mod tests;

/// Array-sorted free variables one attempt may complete.
///
/// The search is a product over the pool below, so this is what keeps it
/// finite.  Three covers every script `#P2b-58` names (`q0106` has three
/// arrays under one binder) and bounds the product at `POOL^3`.
const MAX_COMPLETED_ARRAYS: usize = 3;

/// Default values tried per array.
const MAX_DEFAULT_CANDIDATES: usize = 6;

/// Default *combinations* across all completed arrays.
const MAX_COMBINATIONS: usize = 24;

/// Assertion-DAG nodes above which an attempt declines before it starts.
///
/// The certificate is a *validity* query per universal plus one for the
/// assertions, and a goal this module could actually discharge is small by
/// construction — the whole `#P2b-58` family is two to five assertions.  The
/// cap is what keeps a large benchmark from paying for a search that would
/// decline anyway.
const MAX_GOAL_NODES: usize = 4_096;

/// Quantifier-free certificate queries one attempt may spend in total.
///
/// Each query is a fresh, budgeted, quantifier-free solve; this bounds the
/// cost of the whole attempt independently of how the search goes.
const MAX_CERTIFICATE_QUERIES: usize = 96;

/// Boolean conflicts one certificate query may spend.
///
/// A deterministic budget, not a clock: the certificate's verdict must be a
/// property of the tree and not of the machine (decision (9)).  A query that
/// runs out answers `Unknown`, which this module reads as "not certified".
const CERTIFICATE_CONFLICT_BUDGET: u64 = 20_000;

/// One budget shared by every proposal stage and independent array group.
struct QueryBudget {
    used: usize,
    deadline: Option<nixie_time::Instant>,
    conflicts: Option<u64>,
    decisions: Option<u64>,
}
impl QueryBudget {
    fn for_solver(solver: &Solver) -> Self {
        let conflicts = (solver.config.max_conflicts > 0).then(|| {
            let sat = solver
                .sat
                .max_conflicts()
                .map(|limit| limit.saturating_sub(solver.sat.stats().conflicts))
                .unwrap_or(solver.config.max_conflicts);
            let theory = solver
                .check_theory_conflict_ceiling
                .saturating_sub(solver.statistics.conflicts);
            let bv = solver
                .config
                .max_conflicts
                .saturating_sub(solver.bv.conflicts_spent());
            sat.min(theory).min(bv)
        });
        let decisions = solver
            .sat
            .max_decisions()
            .map(|limit| limit.saturating_sub(solver.sat.stats().decisions));
        Self {
            used: 0,
            deadline: solver.check_deadline,
            conflicts,
            decisions,
        }
    }
    fn start(
        &mut self,
        goal: TermId,
        manager: &TermManager,
        logic: Option<&str>,
    ) -> Option<Solver> {
        if self.used >= MAX_CERTIFICATE_QUERIES
            || self.conflicts == Some(0)
            || self.decisions == Some(0)
            || manager
                .get(goal)
                .is_none_or(|t| t.sort != manager.sorts.bool_sort)
            || contains_quantifier(goal, manager)
        {
            return None;
        }
        let mut solver = Solver::new();
        solver.set_logic(logic.unwrap_or("ALL"));
        solver.config.max_conflicts = self
            .conflicts
            .unwrap_or(CERTIFICATE_CONFLICT_BUDGET)
            .min(CERTIFICATE_CONFLICT_BUDGET);
        solver.config.max_decisions = self.decisions.unwrap_or(0);
        if let Some(deadline) = self.deadline {
            let remaining = deadline.checked_duration_since(nixie_time::Instant::now())?;
            let millis = u64::try_from(remaining.as_millis()).ok()?;
            if millis == 0 {
                return None;
            }
            solver.config.timeout_ms = millis;
        }
        self.used += 1;
        Some(solver)
    }
    fn finish(&mut self, solver: &Solver) {
        if let Some(left) = self.conflicts.as_mut() {
            let spent = solver
                .sat
                .stats()
                .conflicts
                .saturating_add(solver.statistics.conflicts)
                .saturating_add(solver.bv.conflicts_spent());
            *left = left.saturating_sub(spent);
        }
        if let Some(left) = self.decisions.as_mut() {
            *left = left.saturating_sub(solver.sat.stats().decisions);
        }
    }
}

/// Maximal quantifier sub-terms, plus the free symbols an attempt must pin.
struct Goal {
    /// The assertions, unchanged.
    assertions: Vec<TermId>,
    /// Every maximal `forall` sub-term of the assertion set, deduplicated and
    /// in first-encounter order so the attempt is deterministic.
    universals: Vec<TermId>,
    /// The array-sorted free variables to complete, in first-encounter order.
    arrays: Vec<TermId>,
    /// `scalar -> value`, the pins taken from the candidate model.
    scalar_pins: FxHashMap<TermId, TermId>,
    /// Every maximal `exists` sub-term at positive polarity, certified by a
    /// witness among the goal's points (`#P2b-63`, `declined`).
    existentials: Vec<TermId>,
    /// Ground terms left at the candidate model's value rather than
    /// completed — ground applications of uninterpreted functions and ground
    /// reads of arrays only ever read at ground indices (`#P2b-63`,
    /// `declined`); empty on every goal the completion took before.
    ground_values: FxHashMap<TermId, TermId>,
    /// `(original, dual)` for every quantifier sub-term at negative polarity
    /// (`polarity`): the dual is listed in `universals` / `existentials`, and
    /// the original is `false` when the dual is certified.
    negations: Vec<(TermId, TermId)>,
    /// Facts every query of the certificate is read under: for a printed
    /// model, that its uninterpreted-sort witnesses are pairwise distinct
    /// (`printed`); empty for the completion's own searches.
    hypotheses: Vec<TermId>,
}

impl Solver {
    /// Try to publish `Sat` for a quantified array goal by completing the
    /// arrays the candidate model leaves partial and certifying the result.
    ///
    /// Returns `true` only with a *certified* completion in hand, and installs
    /// it into [`Solver::model`] so `(get-model)` prints the interpretation the
    /// certificate verified rather than the partial candidate.  A `false`
    /// leaves the solver exactly as it was found.
    pub(super) fn certify_sat_by_array_completion(&mut self, manager: &mut TermManager) -> bool {
        let original = self.model.clone();
        // Already completed in this check (at the MBQI saturation point, see
        // `check_core`): the model carries the certified interpretation.
        if original
            .as_ref()
            .is_some_and(|model| self.completion_already_installed(model))
        {
            return true;
        }
        let Some((goal, completion)) = self.search_certified_completion(manager) else {
            return false;
        };
        self.install_completed_model(&goal, &completion, manager);
        // The gate every quantified `Sat` exit of `check_core` passes, run on
        // the model that will actually be published.  The certificate already
        // implies it; a disagreement means the two readings differ, and then
        // the original model is what stays.
        if self.model_refutes_assertions(manager) {
            self.model = original;
            self.certified_array_model = None;
            return false;
        }
        true
    }

    /// Whether `model` is exactly the model a completion installed earlier in
    /// this `check` (at MBQI's saturation point, then again at the exit).
    /// Equality of the whole assignment map, not a look at the arrays' values:
    /// a model that merely binds an array to a value term was not certified.
    fn completion_already_installed(&self, model: &Model) -> bool {
        self.certified_array_model
            .as_ref()
            .is_some_and(|certified| certified == model.assignments())
    }

    /// The search behind [`Self::certify_sat_by_array_completion`]: the goal
    /// and a certified completion of its arrays, or `None`.
    ///
    /// Two searches, cheapest first: one constant array per array over the
    /// pooled defaults (`#P2b-58`), then a default plus pinned points
    /// (`pinned`, decision (41)).  Every candidate is first *evaluated* on a
    /// finite sample — the assertions, each universal replaced by its
    /// instances at the goal's own points and at one point they do not name —
    /// and only a candidate the evaluation cannot refute costs a certificate
    /// query.  The evaluation only ever discards (a definite `false` at a
    /// sampled point is a counterexample the certificate would find), so it
    /// changes which candidates are *tried*, never what is accepted.
    fn search_certified_completion(
        &mut self,
        manager: &mut TermManager,
    ) -> Option<(Goal, FxHashMap<TermId, TermId>)> {
        if !self.has_quantifiers || self.certificate_assertions.is_empty() {
            return None;
        }
        let assignments = self
            .model
            .as_ref()
            .map(|m| m.assignments().clone())
            .unwrap_or_default();
        let assertions = self.certificate_assertions.clone();
        if !is_small_enough_to_certify(&assertions, manager) {
            return None;
        }
        let goal = Goal::build(&assertions, &assignments, manager)?;
        let logic = self.logic.clone();
        let mut queries = QueryBudget::for_solver(self);
        // The joint search first, exactly as before whenever it is within its
        // bound, so a goal it certified keeps the interpretation it had.
        if goal.arrays.len() <= MAX_COMPLETED_ARRAYS
            && let Some(completion) = self.search_goal_completion(
                &goal,
                &assignments,
                manager,
                logic.as_deref(),
                &mut queries,
            )
        {
            return Some((goal, completion));
        }
        // Then one search per independent group (`groups`), and the one
        // certificate over every assertion on the union of what they found.
        let groups = groups::array_groups(&goal.arrays, &goal.assertions, manager);
        if groups.len() < 2 {
            return None;
        }
        let mut merged: FxHashMap<TermId, TermId> = FxHashMap::default();
        for group in &groups {
            let sub_goal = goal.restricted_to(group, manager)?;
            let completion = self.search_goal_completion(
                &sub_goal,
                &assignments,
                manager,
                logic.as_deref(),
                &mut queries,
            )?;
            merged.extend(completion);
        }
        goal.certificate_passes(self, &merged, manager, logic.as_deref(), &mut queries)
            .then_some((goal, merged))
    }

    /// One search over `goal`'s arrays: a constant array per array over the
    /// pooled defaults, then (over an `Int` / `Real` index) the candidate's
    /// own points over a pooled default (`infinite`), then a default plus
    /// pinned points (`pinned`).  `None` when none certifies.
    fn search_goal_completion(
        &self,
        goal: &Goal,
        assignments: &FxHashMap<TermId, TermId>,
        manager: &mut TermManager,
        logic: Option<&str>,
        queries: &mut QueryBudget,
    ) -> Option<FxHashMap<TermId, TermId>> {
        let pools = goal.default_pools(assignments, manager);
        if pools.iter().any(Vec::is_empty) {
            return None;
        }
        let points = goal.points_by_sort(manager);
        let samples = goal.sample_instances(&points, manager)?;
        for combination in Combinations::new(&pools) {
            let mut completion: FxHashMap<TermId, TermId> = FxHashMap::default();
            for (&array, &default) in goal.arrays.iter().zip(combination.iter()) {
                let sort = manager.get(array).map(|d| d.sort)?;
                let interpretation = const_array(sort, default, manager);
                completion.insert(array, interpretation);
            }
            if self.completion_refuted_by_evaluation(goal, &completion, &samples, manager) {
                continue;
            }
            if goal.certificate_passes(self, &completion, manager, logic, queries) {
                return Some(completion);
            }
            if queries.used >= MAX_CERTIFICATE_QUERIES {
                break;
            }
        }
        if let Some(completion) = self.search_candidate_point_completion(
            goal,
            assignments,
            &samples,
            manager,
            logic,
            queries,
        ) {
            return Some(completion);
        }
        self.search_pinned_completion(goal, &samples, &points, manager, logic, queries)
    }

    /// Whether `completion` (with the scalar pins) makes some assertion
    /// definitely `false` once every universal is replaced by its sampled
    /// instances (`samples`).  See [`Self::search_certified_completion`].
    fn completion_refuted_by_evaluation(
        &self,
        goal: &Goal,
        completion: &FxHashMap<TermId, TermId>,
        samples: &FxHashMap<TermId, TermId>,
        manager: &mut TermManager,
    ) -> bool {
        let mut interpretation = Model::new();
        for (&symbol, &value) in goal.scalar_pins.iter().chain(completion.iter()) {
            interpretation.set(symbol, value);
        }
        goal.assertions.iter().any(|&assertion| {
            let sampled = manager.substitute(assertion, samples);
            let sampled = manager.substitute(sampled, &goal.ground_values);
            matches!(
                self.eval_under_interpretation(sampled, &interpretation, manager),
                EvalOutcome::Value(EvalVal::Bool(false))
            )
        })
    }

    /// Record the certified interpretation in the published model.
    ///
    /// Each array variable is bound to the term the certificate was
    /// discharged over — `((as const A) d)`, or a `store` chain over it — so
    /// what `(get-model)` prints and what was verified are the same object.
    ///
    /// Installing *replaces* an interpretation, so every other entry whose
    /// term mentions a completed array is dropped first: a read
    /// `(select a k) ↦ v` or an atom over one describes the candidate model,
    /// not the certified one, and `Solver::model_value_in` answers
    /// `(get-value)` from an entry before it evaluates anything.  With the
    /// entry gone the evaluator reads the term through the installed value.
    fn install_completed_model(
        &mut self,
        goal: &Goal,
        completion: &FxHashMap<TermId, TermId>,
        manager: &TermManager,
    ) {
        let model = self.model.get_or_insert_with(Model::new);
        let completed: FxHashSet<TermId> = goal.arrays.iter().copied().collect();
        let mut stale: Vec<TermId> = model
            .assignments()
            .keys()
            .copied()
            .filter(|&term| !completed.contains(&term) && mentions_any(term, &completed, manager))
            .collect();
        stale.sort_unstable_by_key(|term| term.raw());
        for term in stale {
            model.remove(term);
        }
        for &array in &goal.arrays {
            if let Some(&value) = completion.get(&array) {
                model.set(array, value);
            }
        }
        self.certified_array_model = Some(model.assignments().clone());
    }
}

/// Whether `term` has one of `targets` as a sub-term.
fn mentions_any(term: TermId, targets: &FxHashSet<TermId>, manager: &TermManager) -> bool {
    let mut stack: Vec<TermId> = vec![term];
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut children: Vec<TermId> = Vec::new();
    while let Some(current) = stack.pop() {
        if targets.contains(&current) {
            return true;
        }
        if !visited.insert(current) {
            continue;
        }
        let Some(data) = manager.get(current) else {
            continue;
        };
        children.clear();
        children.extend(nixie_core::ast::traversal::get_children(&data.kind));
        stack.extend(children.iter().copied());
    }
    false
}

/// The array-sorted free variables of `assertions` in first-encounter order,
/// and the candidate model's value of every other free symbol it gives one.
///
/// A scalar with no value in the candidate model is left out of the pins:
/// the certificate is a *validity* query, so a symbol it does not interpret
/// can only make the query harder to discharge, never the conclusion weaker.
fn free_symbols(
    assertions: &[TermId],
    assignments: &FxHashMap<TermId, TermId>,
    manager: &TermManager,
) -> Option<(Vec<TermId>, FxHashMap<TermId, TermId>)> {
    let mut arrays: Vec<TermId> = Vec::new();
    let mut scalar_pins: FxHashMap<TermId, TermId> = FxHashMap::default();
    let mut seen: FxHashSet<TermId> = FxHashSet::default();
    for &assertion in assertions {
        let mut free: Vec<TermId> = manager.free_vars_including_patterns(assertion);
        // `free_vars_including_patterns` answers from a set, so order it by
        // the id the term manager already assigned: the attempt's combination
        // order — and hence its verdict — must not depend on a hash iteration
        // order.
        free.sort_unstable_by_key(|term| term.raw());
        for var in free {
            if !seen.insert(var) {
                continue;
            }
            let data = manager.get(var)?;
            if is_array_sort(data.sort, manager) {
                arrays.push(var);
            } else if let Some(&value) = assignments.get(&var) {
                scalar_pins.insert(var, value);
            }
        }
    }
    Some((arrays, scalar_pins))
}

impl Goal {
    /// Classify the assertion set for the completion's search, or decline.
    fn build(
        assertions: &[TermId],
        assignments: &FxHashMap<TermId, TermId>,
        manager: &mut TermManager,
    ) -> Option<Self> {
        let quantifiers = polarity::collect_quantifiers(assertions, manager)?;
        if quantifiers.universals.is_empty() {
            // Nothing to complete under a binder: an `exists`-only goal keeps
            // the candidate's Skolem witness, which the published-model
            // certificate (`printed`) then checks as printed.
            return None;
        }
        let (mut arrays, scalar_pins) = free_symbols(assertions, assignments, manager)?;
        // Where the completion used to decline — an uninterpreted function
        // in the goal, or more arrays than it searches over — the symbols the
        // universals never read through a binder are interpreted from the
        // candidate model instead (`#P2b-63`); every other goal is classified
        // exactly as before.
        let mut ground_values: FxHashMap<TermId, TermId> = FxHashMap::default();
        let fix_arrays = arrays.len() > MAX_COMPLETED_ARRAYS;
        if fix_arrays || declined::has_uninterpreted_application(assertions, manager) {
            let (completed, values) = declined::interpret_from_candidate(
                assertions,
                &arrays,
                assignments,
                &scalar_pins,
                fix_arrays,
                manager,
            )?;
            arrays = completed;
            ground_values = values;
        }
        // The bound is on a *group* of arrays some assertion mentions
        // together (`groups`): four arrays each under its own binder are four
        // one-array searches.
        if arrays.is_empty()
            || groups::largest_group(&arrays, assertions, manager) > MAX_COMPLETED_ARRAYS
        {
            return None;
        }
        Some(Self {
            assertions: assertions.to_vec(),
            universals: quantifiers.universals,
            arrays,
            scalar_pins,
            existentials: quantifiers.existentials,
            ground_values,
            negations: quantifiers.negations,
            hypotheses: Vec::new(),
        })
    }

    /// `query` read under the goal's hypotheses.
    fn under_hypotheses(&self, query: TermId, manager: &mut TermManager) -> TermId {
        if self.hypotheses.is_empty() {
            return query;
        }
        let mut parts = self.hypotheses.clone();
        parts.push(query);
        manager.mk_and(parts)
    }

    /// The default values tried for each array, in a deterministic order.
    ///
    /// The pool is drawn from what the goal itself makes plausible — the
    /// element-sort values the candidate model already committed to, then the
    /// element-sort literals the script spells out, then the two ends of the
    /// sort — which is the same "values the goal makes plausible" rule
    /// [`crate::mbqi::model_certify`] uses for a function default.
    fn default_pools(
        &self,
        assignments: &FxHashMap<TermId, TermId>,
        manager: &mut TermManager,
    ) -> Vec<Vec<TermId>> {
        let mut literals: Vec<TermId> = Vec::new();
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        for &assertion in &self.assertions {
            collect_constants(assertion, manager, &mut literals, &mut seen);
        }
        let mut model_values: Vec<TermId> = assignments.values().copied().collect();
        model_values.sort_unstable_by_key(|term| term.raw());
        model_values.dedup();

        self.arrays
            .iter()
            .map(|&array| {
                let element = element_sort(array, manager);
                let mut pool: Vec<TermId> = Vec::new();
                let mut pool_keys: FxHashSet<TermId> = FxHashSet::default();
                let push = |candidate: TermId,
                            pool: &mut Vec<TermId>,
                            keys: &mut FxHashSet<TermId>,
                            manager: &TermManager| {
                    if pool.len() >= MAX_DEFAULT_CANDIDATES {
                        return;
                    }
                    if !manager
                        .get(candidate)
                        .is_some_and(|d| Some(d.sort) == element)
                    {
                        return;
                    }
                    if keys.insert(candidate) {
                        pool.push(candidate);
                    }
                };
                for &value in &model_values {
                    push(value, &mut pool, &mut pool_keys, manager);
                }
                for &literal in &literals {
                    push(literal, &mut pool, &mut pool_keys, manager);
                }
                if let Some(element) = element {
                    for extreme in sort_extremes(element, manager) {
                        push(extreme, &mut pool, &mut pool_keys, manager);
                    }
                }
                pool
            })
            .collect()
    }

    /// The quantifier-free certificate for one completion.
    ///
    /// Every step is a validity query discharged by refuting its negation; see
    /// the module docs for why only that direction is taken.  A closed
    /// instance is *evaluated* exactly instead of queried: `true` is what the
    /// query's `Unsat` would conclude and `false` what its `Sat` would, so the
    /// evaluation changes which queries are spent, never what is accepted.
    fn certificate_passes(
        &self,
        solver: &Solver,
        completion: &FxHashMap<TermId, TermId>,
        manager: &mut TermManager,
        logic: Option<&str>,
        queries: &mut QueryBudget,
    ) -> bool {
        let substitution = self.full_substitution(completion);
        let dual_of: FxHashMap<TermId, TermId> = self
            .negations
            .iter()
            .map(|&(original, dual)| (dual, original))
            .collect();
        let extra_points = completion_points(completion, manager);

        // Step 1: every maximal `forall` is certified *true* under the
        // completion where it can be (and one that cannot is left
        // undetermined for step 2, `undetermined`).  The bound variables become fresh reserved constants, so
        // the query is quantifier-free and the bound name can never be
        // confused with a free one of the same name — which is exactly the
        // collision shape of `rk8/atk/f5_binder_collide_index.smt2`.  The dual
        // `∀x⃗. ¬φ` of a negated `exists` certifies that `exists` *false*
        // (`polarity`); where it does not, the `exists` itself may still be
        // certified true by a witness, and the assertions then decide.
        let mut truths: FxHashMap<TermId, TermId> = FxHashMap::default();
        for (position, &universal) in self.universals.iter().enumerate() {
            let original = dual_of.get(&universal).copied();
            if self.universal_certified(
                solver,
                universal,
                position,
                &substitution,
                manager,
                logic,
                queries,
            ) {
                truths.insert(universal, manager.mk_true());
                if let Some(original) = original {
                    truths.insert(original, manager.mk_false());
                }
                continue;
            }
            let Some(original) = original else {
                truths.insert(universal, undetermined(manager, "u", position));
                continue;
            };
            if !self.certify_existential(
                solver,
                original,
                position,
                &substitution,
                &extra_points,
                manager,
                logic,
                queries,
            ) {
                truths.insert(original, undetermined(manager, "u", position));
                continue;
            }
            truths.insert(original, manager.mk_true());
        }
        // Step 1b: every maximal `exists` must be certified true by a witness
        // (`#P2b-63`, `declined`); the dual `∃x⃗. ¬φ` of a negated `forall`
        // certifies that `forall` false, and where it does not, the `forall`
        // itself may still be certified true.
        for (position, &existential) in self.existentials.iter().enumerate() {
            let original = dual_of.get(&existential).copied();
            if self.certify_existential(
                solver,
                existential,
                position,
                &substitution,
                &extra_points,
                manager,
                logic,
                queries,
            ) {
                truths.insert(existential, manager.mk_true());
                if let Some(original) = original {
                    truths.insert(original, manager.mk_false());
                }
                continue;
            }
            let Some(original) = original else {
                truths.insert(existential, undetermined(manager, "e", position));
                continue;
            };
            if !self.universal_certified(
                solver,
                original,
                self.universals.len() + position,
                &substitution,
                manager,
                logic,
                queries,
            ) {
                truths.insert(original, undetermined(manager, "e", position));
                continue;
            }
            truths.insert(original, manager.mk_true());
        }

        // Step 2: the assertions themselves.  Evaluated first; where every
        // one evaluates, no query is spent.  Otherwise one query:
        // `(or ¬A₁ … ¬Aₙ)` is `Unsat` exactly when every `Aᵢ` holds under the
        // completion.
        let mut disjuncts: Vec<TermId> = Vec::with_capacity(self.assertions.len());
        let mut all_true = true;
        for &assertion in &self.assertions {
            let grounded = manager.substitute(assertion, &truths);
            let grounded = manager.substitute(grounded, &substitution);
            match evaluate_closed(solver, grounded, manager) {
                Some(false) => return false,
                Some(true) => {}
                None => all_true = false,
            }
            disjuncts.push(manager.mk_not(grounded));
        }
        if all_true {
            return true;
        }
        let refutation = manager.mk_or(disjuncts);
        let refutation = self.under_hypotheses(refutation, manager);
        matches!(
            run_query(refutation, manager, logic, queries),
            Some(SolverResult::Unsat)
        )
    }

    /// The scalar pins, the fixed ground values and `completion`, as one map.
    fn full_substitution(
        &self,
        completion: &FxHashMap<TermId, TermId>,
    ) -> FxHashMap<TermId, TermId> {
        let mut substitution = self.scalar_pins.clone();
        substitution.extend(self.ground_values.iter().map(|(&k, &v)| (k, v)));
        substitution.extend(completion.iter().map(|(&k, &v)| (k, v)));
        substitution
    }

    /// Whether the universal `universal` (listed at `position`) is certified
    /// true under `substitution`: by the point split over an infinite index
    /// sort where it applies (`split`), else by the validity query.
    #[allow(clippy::too_many_arguments)]
    fn universal_certified(
        &self,
        solver: &Solver,
        universal: TermId,
        position: usize,
        substitution: &FxHashMap<TermId, TermId>,
        manager: &mut TermManager,
        logic: Option<&str>,
        queries: &mut QueryBudget,
    ) -> bool {
        if let Some(verdict) = split::universal_by_points(
            solver,
            universal,
            position,
            substitution,
            &self.hypotheses,
            manager,
            logic,
            queries,
        ) {
            return verdict;
        }
        let Some(body) = peel_universal(universal, position, manager) else {
            return false;
        };
        let body = manager.substitute(body, substitution);
        let negated = manager.mk_not(body);
        let negated = self.under_hypotheses(negated, manager);
        matches!(
            run_query(negated, manager, logic, queries),
            Some(SolverResult::Unsat)
        )
    }
}

/// A fresh Boolean constant standing for a quantifier sub-term neither of
/// whose values could be certified.  The assertions' validity query then has
/// to hold for *both* of its values, so an assertion that does not depend on
/// the sub-term — `(=> p (forall …))` under `p = false` — still certifies, and
/// one that does cannot: sound for the same reason every other symbol the
/// query leaves free is.
fn undetermined(manager: &mut TermManager, kind: &str, position: usize) -> TermId {
    let bool_sort = manager.sorts.bool_sort;
    manager.mk_var(
        &reserved_name("qunk", &format!("{kind}{position}")),
        bool_sort,
    )
}

/// The exact value of a closed Boolean term, or `None` when the evaluator
/// cannot fold it to one (a symbol it does not interpret, an array equality).
pub(crate) fn evaluate_closed(
    solver: &Solver,
    term: TermId,
    manager: &mut TermManager,
) -> Option<bool> {
    let term = array_values::fold_array_value_equalities(term, manager);
    match solver.eval_under_interpretation(term, &Model::new(), manager) {
        EvalOutcome::Value(EvalVal::Bool(value)) => Some(value),
        _ => None,
    }
}

/// Every literal `store` index of the completion's interpretations, by sort:
/// the points the interpretation names, which a witness search must try
/// (an `exists` witnessed where the candidate's Skolem constant was read).
fn completion_points(
    completion: &FxHashMap<TermId, TermId>,
    manager: &TermManager,
) -> FxHashMap<SortId, Vec<TermId>> {
    let mut out: FxHashMap<SortId, Vec<TermId>> = FxHashMap::default();
    let mut values: Vec<TermId> = completion.values().copied().collect();
    values.sort_unstable_by_key(|term| term.raw());
    for value in values {
        let mut current = value;
        while let Some(TermKind::Store(inner, index, _)) = manager.get(current).map(|d| &d.kind) {
            if is_literal(*index, manager)
                && let Some(sort) = manager.get(*index).map(|d| d.sort)
            {
                let list = out.entry(sort).or_default();
                if !list.contains(index) {
                    list.push(*index);
                }
            }
            current = *inner;
        }
    }
    out
}

/// Run one quantifier-free certificate query, or `None` when the query budget
/// is spent.
///
/// The sub-solver is budgeted deterministically and carries no clock, so the
/// certificate reproduces on an idle and on a loaded machine alike.  It cannot
/// re-enter this module: the goal handed to it is quantifier-free by
/// construction, and the entry point above requires a quantifier.
fn run_query(
    goal: TermId,
    manager: &mut TermManager,
    logic: Option<&str>,
    queries: &mut QueryBudget,
) -> Option<SolverResult> {
    let goal = array_values::fold_array_value_equalities(goal, manager);
    let mut solver = queries.start(goal, manager, logic)?;
    solver.assert(goal, manager);
    let result = solver.check(manager);
    queries.finish(&solver);
    Some(result)
}

/// The body of a chain of consecutive `forall`s, with every bound variable
/// replaced by a fresh reserved constant, or `None` when the sub-term is not a
/// universal this module handles.
///
/// A chain is peeled rather than a single binder, so
/// `(forall ((k …)) (forall ((k …)) …))` — decision (36)'s "the collision shape
/// with the array name bound **twice**" — is one multi-binder universal and not
/// a nested one.  A quantifier that survives the peel is a genuine
/// alternation and is declined, because the certificate below would not be
/// quantifier-free.
fn peel_universal(term: TermId, position: usize, manager: &mut TermManager) -> Option<TermId> {
    peel_universal_with_vars(term, position, manager).map(|(body, _)| body)
}

/// [`peel_universal`], also returning the fresh constants the bound variables
/// became, in binder order, so a caller can instantiate the body at chosen
/// points (`pinned::Goal::fill_query`).
fn peel_universal_with_vars(
    term: TermId,
    position: usize,
    manager: &mut TermManager,
) -> Option<(TermId, Vec<TermId>)> {
    let mut current = term;
    let mut bound: Vec<(Spur, SortId)> = Vec::new();
    loop {
        let kind = manager.get(current).map(|d| d.kind.clone())?;
        match kind {
            TermKind::Forall { vars, body, .. } => {
                bound.extend(vars.iter().copied());
                current = body;
            }
            _ => break,
        }
    }
    if contains_quantifier(current, manager) {
        return None;
    }
    let mut rename: FxHashMap<TermId, TermId> = FxHashMap::default();
    let mut fresh_vars: Vec<TermId> = Vec::with_capacity(bound.len());
    for (index, (name, sort)) in bound.into_iter().enumerate() {
        let bound_name = manager.resolve_str(name).to_string();
        let bound_var = manager.mk_var(&bound_name, sort);
        let fresh = manager.mk_var(
            &reserved_name("qcert", &format!("{position}_{index}")),
            sort,
        );
        // A chain that binds one name twice keeps the innermost binding,
        // which is the one the body sees; the constant list keeps one entry
        // per *distinct* variable so an instantiation never assigns it twice.
        match rename.insert(bound_var, fresh) {
            None => fresh_vars.push(fresh),
            Some(previous) => {
                if let Some(slot) = fresh_vars.iter_mut().find(|var| **var == previous) {
                    *slot = fresh;
                }
            }
        }
    }
    Some((manager.substitute(current, &rename), fresh_vars))
}

/// Every constant (literal) sub-term of `term`, in first-encounter order.
fn collect_constants(
    term: TermId,
    manager: &TermManager,
    out: &mut Vec<TermId>,
    seen: &mut FxHashSet<TermId>,
) {
    let mut stack: Vec<TermId> = vec![term];
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut children: Vec<TermId> = Vec::new();
    let mut found: Vec<TermId> = Vec::new();
    while let Some(current) = stack.pop() {
        if !visited.insert(current) {
            continue;
        }
        let Some(data) = manager.get(current) else {
            continue;
        };
        if matches!(
            data.kind,
            TermKind::BitVecConst { .. }
                | TermKind::IntConst(_)
                | TermKind::RealConst(_)
                | TermKind::True
                | TermKind::False
        ) {
            found.push(current);
        }
        children.clear();
        children.extend(nixie_core::ast::traversal::get_children(&data.kind));
        stack.extend(children.iter().copied());
    }
    found.sort_unstable_by_key(|term| term.raw());
    for term in found {
        if seen.insert(term) {
            out.push(term);
        }
    }
}

/// Whether `term` carries a quantifier anywhere in it.
fn contains_quantifier(term: TermId, manager: &TermManager) -> bool {
    let mut stack: Vec<TermId> = vec![term];
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut children: Vec<TermId> = Vec::new();
    while let Some(current) = stack.pop() {
        if !visited.insert(current) {
            continue;
        }
        let Some(data) = manager.get(current) else {
            continue;
        };
        if matches!(data.kind, TermKind::Forall { .. } | TermKind::Exists { .. }) {
            return true;
        }
        children.clear();
        children.extend(nixie_core::ast::traversal::get_children(&data.kind));
        stack.extend(children.iter().copied());
    }
    false
}

/// Whether the goal is one an attempt can afford to try: at most
/// [`MAX_GOAL_NODES`] assertion-DAG nodes.
///
/// An uninterpreted application used to decline here as well (it survives
/// into the validity query, where the sub-solver may interpret it any way it
/// likes, so a satisfiable-but-not-valid goal never certifies).  It is now
/// interpreted from the candidate model where it is ground, and declines in
/// `Goal::build` where it is not (`#P2b-63`, `declined`).
fn is_small_enough_to_certify(assertions: &[TermId], manager: &TermManager) -> bool {
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut children: Vec<TermId> = Vec::new();
    while let Some(current) = stack.pop() {
        if !visited.insert(current) {
            continue;
        }
        if visited.len() > MAX_GOAL_NODES {
            return false;
        }
        let Some(data) = manager.get(current) else {
            return false;
        };
        children.clear();
        children.extend(nixie_core::ast::traversal::get_children(&data.kind));
        stack.extend(children.iter().copied());
    }
    true
}

/// Whether `sort` is an array sort.
fn is_array_sort(sort: SortId, manager: &TermManager) -> bool {
    manager
        .sorts
        .get(sort)
        .is_some_and(|s| matches!(s.kind, SortKind::Array { .. }))
}

/// The element sort of an array-sorted term.
fn element_sort(term: TermId, manager: &TermManager) -> Option<SortId> {
    let data = manager.get(term)?;
    match manager.sorts.get(data.sort)?.kind {
        SortKind::Array { range, .. } => Some(range),
        _ => None,
    }
}

/// The two ends of a sort, as a last resort for the default pool.
fn sort_extremes(sort: SortId, manager: &mut TermManager) -> Vec<TermId> {
    let kind = manager.sorts.get(sort).map(|s| s.kind.clone());
    match kind {
        Some(SortKind::BitVec(width)) => {
            let zero = manager.mk_bitvec(num_bigint::BigInt::from(0u8), width);
            let ones = manager.mk_bitvec(
                (num_bigint::BigInt::from(1u8) << width) - num_bigint::BigInt::from(1u8),
                width,
            );
            vec![zero, ones]
        }
        Some(SortKind::Bool) => vec![manager.mk_false(), manager.mk_true()],
        _ => Vec::new(),
    }
}

/// A bounded product over per-position pools (the per-array default pools,
/// or the per-variable instantiation points of `pinned::Goal::fill_query`).
struct Combinations<'a> {
    pools: &'a [Vec<TermId>],
    cursor: Vec<usize>,
    emitted: usize,
    cap: usize,
    done: bool,
}

impl<'a> Combinations<'a> {
    /// The product over `pools`, at most [`MAX_COMBINATIONS`] items.
    fn new(pools: &'a [Vec<TermId>]) -> Self {
        Self::with_cap(pools, MAX_COMBINATIONS)
    }

    /// The product over `pools`, at most `cap` items.
    fn with_cap(pools: &'a [Vec<TermId>], cap: usize) -> Self {
        Self {
            pools,
            cursor: vec![0; pools.len()],
            emitted: 0,
            cap,
            done: pools.is_empty(),
        }
    }
}

impl Iterator for Combinations<'_> {
    type Item = Vec<TermId>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done || self.emitted >= self.cap {
            return None;
        }
        let mut item: Vec<TermId> = Vec::with_capacity(self.pools.len());
        for (pool, &index) in self.pools.iter().zip(self.cursor.iter()) {
            item.push(*pool.get(index)?);
        }
        self.emitted += 1;
        // Odometer, least significant position first.
        let mut position = self.cursor.len();
        loop {
            if position == 0 {
                self.done = true;
                break;
            }
            position -= 1;
            let limit = self.pools.get(position).map_or(0, Vec::len);
            let next = self.cursor.get_mut(position)?;
            *next += 1;
            if *next < limit {
                break;
            }
            *next = 0;
        }
        Some(item)
    }
}

/// The interpretation a completed array is published under: `((as const A) d)`.
pub(super) fn const_array(
    array_sort: SortId,
    default: TermId,
    manager: &mut TermManager,
) -> TermId {
    manager.mk_apply(CONST_ARRAY_FUNC, [default], array_sort)
}

/// Whether `term` is a closed array *value* this module installs: the array
/// constant [`const_array`] builds over a literal default, or a `store` chain
/// over one whose every index and stored value is a literal.
///
/// The renderer prints such a term verbatim and the model evaluator reads a
/// `select` through it; nothing else in the solver assigns an array a value
/// term, so the predicate is exactly "an interpretation the certificate
/// verified".
pub(crate) fn is_array_value(term: TermId, manager: &TermManager) -> bool {
    let mut current = term;
    loop {
        let Some(data) = manager.get(current) else {
            return false;
        };
        match &data.kind {
            TermKind::Store(inner, index, value) => {
                let Some(SortKind::Array { domain, range }) =
                    manager.sorts.get(data.sort).map(|s| &s.kind)
                else {
                    return false;
                };
                if manager.get(*inner).is_none_or(|d| d.sort != data.sort)
                    || manager.get(*index).is_none_or(|d| d.sort != *domain)
                    || manager.get(*value).is_none_or(|d| d.sort != *range)
                    || !is_literal(*index, manager)
                    || !is_literal(*value, manager)
                {
                    return false;
                }
                current = *inner;
            }
            _ => {
                return super::array_axioms::const_array_default(current, manager)
                    .is_some_and(|default| is_literal(default, manager));
            }
        }
    }
}

/// Whether `term` is a literal value of a scalar sort.
fn is_literal(term: TermId, manager: &TermManager) -> bool {
    let Some(data) = manager.get(term) else {
        return false;
    };
    match &data.kind {
        TermKind::BitVecConst { width, .. } => {
            *width > 0
                && manager.sorts.get(data.sort).and_then(|s| s.bitvec_width()) == Some(*width)
        }
        TermKind::IntConst(_) => data.sort == manager.sorts.int_sort,
        TermKind::RealConst(_) => data.sort == manager.sorts.real_sort,
        TermKind::True | TermKind::False => data.sort == manager.sorts.bool_sort,
        _ => false,
    }
}

/// Whether `term` is the array constant [`const_array`] builds.
///
/// The model formatter asks this before it prefers an explicit model entry
/// over the congruence class it would otherwise render an array from; see
/// `Context::array_model_value`.
pub(crate) fn is_const_array(term: TermId, manager: &TermManager) -> bool {
    manager.get(term).is_some_and(|data| match &data.kind {
        TermKind::Apply { func, args } => {
            args.len() == 1 && manager.resolve_str(*func) == CONST_ARRAY_FUNC
        }
        _ => false,
    })
}
