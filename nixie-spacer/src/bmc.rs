//! Bounded Model Checking (BMC) for CHC systems.
//!
//! BMC complements PDR/IC3 by exploring reachability up to a bounded depth.
//! It's particularly effective for finding counterexamples quickly.
//!
//! Reference: Z3's BMC implementation and standard BMC algorithms

use crate::chc::{ChcSystem, PredId, RuleHead};
use crate::reach::{CexState, Counterexample};
use crate::smt::{SmtError, SmtSolver};
use nixie_core::{SortId, TermId, TermManager};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use thiserror::Error;
use tracing::{debug, trace};

/// Errors that can occur during BMC
#[derive(Error, Debug)]
pub enum BmcError {
    /// The CHC system is empty
    #[error("empty CHC system")]
    EmptySystem,
    /// No query found in the system
    #[error("no query found in CHC system")]
    NoQuery,
    /// No entry (init) rule found in the system
    #[error("no init rule found in CHC system")]
    NoInitRule,
    /// SMT solver error
    #[error("SMT error: {0}")]
    Smt(#[from] SmtError),
    /// Internal error
    #[error("internal error: {0}")]
    Internal(String),
}

/// Result of a BMC / k-induction check
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BmcResult {
    /// Property holds up to the given bound
    /// (does not prove safety, only that no counterexample was found)
    Safe(u32),
    /// Counterexample found at the given depth
    Unsafe(u32),
    /// Could not determine (e.g. non-linear CHC, solver returned Unknown)
    Unknown,
}

/// Configuration for BMC
#[derive(Debug, Clone)]
pub struct BmcConfig {
    /// Maximum depth to explore
    pub max_depth: u32,
    /// Enable k-induction
    pub use_kinduction: bool,
    /// Verbosity level (0 = quiet, 1 = normal, 2 = verbose)
    pub verbosity: u32,
}

impl Default for BmcConfig {
    fn default() -> Self {
        Self {
            max_depth: 100,
            use_kinduction: false,
            verbosity: 0,
        }
    }
}

/// Statistics from BMC
#[derive(Debug, Clone, Default)]
pub struct BmcStats {
    /// Maximum depth reached
    pub max_depth_reached: u32,
    /// Number of SMT queries
    pub num_smt_queries: u32,
    /// Number of unrollings
    pub num_unrollings: u32,
}

// ========  ========
// Helper: per-predicate step variables
// ========  ========

/// Create per-step state variables for a predicate's parameters.
///
/// For a predicate `P(p0:S0, p1:S1, …)` at step `step`, this creates
/// `mk_var("P_step{step}_param{j}", Sj)` for each parameter `j`.
fn make_step_vars(
    terms: &mut TermManager,
    pred_name: &str,
    param_sorts: &[SortId],
    step: u32,
) -> Vec<TermId> {
    param_sorts
        .iter()
        .enumerate()
        .map(|(j, &sort)| {
            let name = format!("{}_step{}_param{}", pred_name, step, j);
            terms.mk_var(&name, sort)
        })
        .collect()
}

/// Build a substitution map from a `PredicateApp`'s args to per-step vars.
///
/// `app_args[j]` (the TermId used as the j-th arg in the predicate application)
/// maps to `step_vars[j]`.
fn subst_from_args(app_args: &[TermId], step_vars: &[TermId]) -> FxHashMap<TermId, TermId> {
    app_args
        .iter()
        .copied()
        .zip(step_vars.iter().copied())
        .collect()
}

// ========  ========
// Bounded Model Checker
// ========  ========

/// Bounded Model Checker
pub struct Bmc<'a> {
    /// Term manager for creating formulas
    terms: &'a mut TermManager,
    /// The CHC system to check
    system: &'a ChcSystem,
    /// Configuration
    config: BmcConfig,
    /// Statistics
    stats: BmcStats,
    /// Current counterexample (if found)
    counterexample: Option<Counterexample>,
}

impl<'a> Bmc<'a> {
    /// Create a new BMC instance
    pub fn new(terms: &'a mut TermManager, system: &'a ChcSystem) -> Self {
        Self::with_config(terms, system, BmcConfig::default())
    }

    /// Create a new BMC instance with configuration
    pub fn with_config(
        terms: &'a mut TermManager,
        system: &'a ChcSystem,
        config: BmcConfig,
    ) -> Self {
        Self {
            terms,
            system,
            config,
            stats: BmcStats::default(),
            counterexample: None,
        }
    }

    /// Run bounded model checking
    pub fn check(&mut self) -> Result<BmcResult, BmcError> {
        // Validate system
        if self.system.is_empty() {
            return Err(BmcError::EmptySystem);
        }

        if self.system.queries().next().is_none() {
            return Err(BmcError::NoQuery);
        }

        // If k-induction is requested, delegate entirely to it
        if self.config.use_kinduction {
            return self.run_kinduction();
        }

        // Pure BMC: try each depth 0..=max_depth
        for depth in 0..=self.config.max_depth {
            self.stats.max_depth_reached = depth;
            debug!("BMC: checking depth {}", depth);

            match self.check_bad_at_depth(depth)? {
                BmcResult::Unsafe(k) => {
                    debug!("BMC: counterexample found at depth {}", k);
                    return Ok(BmcResult::Unsafe(k));
                }
                BmcResult::Unknown => {
                    return Ok(BmcResult::Unknown);
                }
                BmcResult::Safe(_) => {
                    self.stats.num_unrollings += 1;
                }
            }
        }

        Ok(BmcResult::Safe(self.config.max_depth))
    }

    // ========  ========
    // Core BMC query: Φ_k = Init(s₀) ∧ Trans(s₀,s₁) ∧ … ∧ Trans(s_{k-1},s_k) ∧ Bad(s_k)
    // ========  ========

    /// Check whether a bad state is reachable at exactly depth `k`.
    ///
    /// Returns `Unsafe(k)` with a witness if SAT, `Safe(k)` if UNSAT,
    /// or `Unknown` if the solver could not decide.
    ///
    /// **Soundness invariant**: `Unsafe` is only returned when the SMT solver
    /// returns SAT on the full unrolling formula.
    pub fn check_bad_at_depth(&mut self, k: u32) -> Result<BmcResult, BmcError> {
        trace!("BMC check_bad_at_depth({})", k);
        self.stats.num_smt_queries = self.stats.num_smt_queries.saturating_add(1);

        // We only handle the *single-predicate linear* case to remain sound.
        // Non-linear CHC (multiple distinct predicates in rule body) would
        // require a more complex encoding – we conservatively return Unknown.
        let pred_count = self.system.predicates().count();
        if pred_count > 1 {
            // Multi-predicate systems may be non-linear; return Unknown.
            debug!(
                "BMC: {} predicates – returning Unknown for safety",
                pred_count
            );
            return Ok(BmcResult::Unknown);
        }

        // Identify the single predicate (if any)
        let pred_info = match self.system.predicates().next() {
            Some(p) => p.clone(),
            None => return Ok(BmcResult::Safe(k)), // No predicates → trivially safe
        };

        let pred_id = pred_info.id;
        let pred_name = pred_info.name.clone();
        let param_sorts: Vec<SortId> = pred_info.params.iter().copied().collect();

        // Build step variables s₀, s₁, …, sₖ
        // step_vars[i] = Vec<TermId> of step-i state variables
        let step_vars: Vec<Vec<TermId>> = (0..=k)
            .map(|step| make_step_vars(self.terms, &pred_name, &param_sorts, step))
            .collect();

        let mut conjuncts: Vec<TermId> = Vec::new();

        // ======== Init constraint: Init(s₀) ========
        let mut init_added = false;
        for rule in self.system.entries() {
            // Entry rules have no predicates in the body; they establish s₀.
            // They must have a non-query head (i.e. head predicate = pred_id).
            if rule.head_predicate() != Some(pred_id) {
                continue;
            }
            if let RuleHead::Predicate(ref head_app) = rule.head {
                // Map head args → step-0 vars
                let subst = subst_from_args(&head_app.args, &step_vars[0]);
                let init_c = self.terms.substitute(rule.body.constraint, &subst);
                conjuncts.push(init_c);
                init_added = true;
            }
        }
        if !init_added {
            return Err(BmcError::NoInitRule);
        }

        // ======== Transition constraints: Trans(sᵢ, sᵢ₊₁) for i = 0..k-1 ========
        // The transition relation is the DISJUNCTION of all matching rules:
        // a nondeterministic system may advance via any one of its rules, so
        // conjoining them (which is what a naive encoding would do) makes
        // contradictory rules like x'=x+1 and x'=x-1 render the whole
        // unrolling UNSAT and yields an unsound Safe answer.
        for i in 0..k {
            // Collect each matching rule's substituted transition as a disjunct.
            let mut disjuncts: Vec<TermId> = Vec::new();
            for rule in self.system.rules_by_head(pred_id) {
                // Skip init rules
                if rule.body.predicates.is_empty() {
                    continue;
                }
                // Skip if body references a different predicate
                if rule.body.predicates.iter().any(|app| app.pred != pred_id) {
                    continue;
                }
                if let (Some(body_app), RuleHead::Predicate(head_app)) =
                    (rule.body.predicates.first(), &rule.head)
                {
                    // body_app.args are the "current state" variables (step i)
                    // head_app.args are the "next state" variables (step i+1)
                    let mut subst = subst_from_args(&body_app.args, &step_vars[i as usize]);
                    subst.extend(subst_from_args(&head_app.args, &step_vars[i as usize + 1]));
                    let trans_c = self.terms.substitute(rule.body.constraint, &subst);
                    disjuncts.push(trans_c);
                }
            }
            if disjuncts.is_empty() {
                // No transition rule: no way to advance state, so no
                // counterexample can exist beyond depth 0.
                debug!(
                    "BMC: no transition rule for pred {:?} – safe at depth > 0",
                    pred_id
                );
                return Ok(BmcResult::Safe(k));
            }
            let step_trans = self.terms.mk_or(disjuncts);
            conjuncts.push(step_trans);
        }

        // ======== Bad state: Bad(sₖ) ========
        let mut bad_added = false;
        for query in self.system.queries() {
            for body_app in &query.body.predicates {
                if body_app.pred != pred_id {
                    continue;
                }
                let subst = subst_from_args(&body_app.args, &step_vars[k as usize]);
                let bad_c = self.terms.substitute(query.body.constraint, &subst);
                conjuncts.push(bad_c);
                bad_added = true;
            }
        }
        if !bad_added {
            // No query references this predicate – trivially safe at depth k
            return Ok(BmcResult::Safe(k));
        }

        // ======== Check satisfiability ========
        let formula = self.terms.mk_and(conjuncts);

        let mut smt = SmtSolver::new(self.terms, self.system);
        smt.push();
        smt.assert(formula);
        let sat_result = smt.check_sat();
        let is_sat = match sat_result {
            Ok(v) => v,
            Err(SmtError::Unknown) => {
                smt.pop();
                return Ok(BmcResult::Unknown);
            }
            Err(e) => {
                smt.pop();
                return Err(BmcError::Smt(e));
            }
        };

        if is_sat {
            // Extract a concrete counterexample from the model.
            let cex = build_counterexample_from_model(&mut smt, pred_id, &step_vars, k);
            smt.pop();
            self.counterexample = Some(cex);
            Ok(BmcResult::Unsafe(k))
        } else {
            smt.pop();
            Ok(BmcResult::Safe(k))
        }
    }

    // ========  ========
    // K-induction
    // ========  ========

    /// Run k-induction from depth 1 up to `max_depth`.
    ///
    /// If every attempted `k` returns [`BmcResult::Unknown`], this reports
    /// `Unknown` overall rather than fabricating `Safe(max_depth)`.
    /// `check_kinduction(k)`'s base-case loop (`0..=k`) returns `Unknown`
    /// and stops at the *first* depth the SMT solver can't decide -- it
    /// does not necessarily re-verify every depth up to `k` on every call.
    /// Because the underlying query is deterministic, an `Unknown` at some
    /// depth `i` tends to recur at every later `k >= i` too, so hitting
    /// `Unknown` on every iteration up to `max_depth` does *not* mean
    /// depths `i..=max_depth` were ever actually verified free of a
    /// counterexample -- it means the solver could never get past depth
    /// `i`. Claiming `Safe(max_depth)` in that situation would silently
    /// assert bounded safety that was never actually checked.
    fn run_kinduction(&mut self) -> Result<BmcResult, BmcError> {
        for k in 1..=self.config.max_depth {
            self.stats.max_depth_reached = k;
            debug!("K-induction: trying k={}", k);
            match self.check_kinduction(k)? {
                BmcResult::Safe(d) => return Ok(BmcResult::Safe(d)),
                BmcResult::Unsafe(d) => return Ok(BmcResult::Unsafe(d)),
                BmcResult::Unknown => {
                    // Try a larger k
                    self.stats.num_unrollings += 1;
                }
            }
        }
        // Every k in 1..=max_depth came back Unknown: no inductive proof
        // was found and no depth range was conclusively verified safe.
        Ok(BmcResult::Unknown)
    }

    /// Sound k-induction check.
    ///
    /// 1. **Base case**: for i in 0..=k, verify `check_bad_at_depth(i)`.
    ///    Any `Unsafe(i)` is immediately propagated.
    ///
    /// 2. **Inductive step**: check UNSAT of
    ///    `P(s₀) ∧ … ∧ P(s_{k-1}) ∧ Trans(s₀,s₁) ∧ … ∧ Trans(s_{k-1},sₖ) ∧ Bad(sₖ)`
    ///    where `P(sᵢ) = ¬Bad(sᵢ)`.
    ///    * UNSAT  → `Safe` (k-inductive proof found)
    ///    * SAT    → `Unknown` (NOT Unsafe – only base case can yield Unsafe)
    ///
    /// **Soundness invariant**: `Unsafe` is returned only when the base case
    /// finds a real SAT witness.  The inductive-step formula being SAT merely
    /// means k-induction cannot prove safety at this k.
    pub fn check_kinduction(&mut self, k: u32) -> Result<BmcResult, BmcError> {
        trace!("BMC check_kinduction({})", k);

        if k == 0 {
            return Ok(BmcResult::Unknown);
        }

        // ======== Base case: check depths 0..=k ========
        for i in 0..=k {
            match self.check_bad_at_depth(i)? {
                BmcResult::Unsafe(d) => return Ok(BmcResult::Unsafe(d)),
                BmcResult::Unknown => return Ok(BmcResult::Unknown),
                BmcResult::Safe(_) => {}
            }
        }

        // ======== Inductive step ========
        // Only sound for single-predicate linear CHC
        let pred_count = self.system.predicates().count();
        if pred_count > 1 {
            return Ok(BmcResult::Unknown);
        }

        let pred_info = match self.system.predicates().next() {
            Some(p) => p.clone(),
            None => return Ok(BmcResult::Safe(k)),
        };

        let pred_id = pred_info.id;
        let pred_name = pred_info.name.clone();
        let param_sorts: Vec<SortId> = pred_info.params.iter().copied().collect();

        // Build step variables s₀ … sₖ  (k+1 steps)
        let step_vars: Vec<Vec<TermId>> = (0..=k)
            .map(|step| {
                make_step_vars(
                    self.terms,
                    &format!("{}_ind", pred_name),
                    &param_sorts,
                    step,
                )
            })
            .collect();

        let mut conjuncts: Vec<TermId> = Vec::new();

        // Collect the "Bad" formula template (without step substitution yet)
        let mut bad_templates: Vec<(SmallVec<[TermId; 4]>, TermId)> = Vec::new();
        for query in self.system.queries() {
            for body_app in &query.body.predicates {
                if body_app.pred == pred_id {
                    bad_templates.push((body_app.args.clone(), query.body.constraint));
                }
            }
        }

        // ¬Bad(sᵢ) for i = 0 .. k-1  (the induction hypothesis)
        for i in 0..k {
            for (args, bad_constraint) in &bad_templates {
                let subst = subst_from_args(args, &step_vars[i as usize]);
                let bad_at_i = self.terms.substitute(*bad_constraint, &subst);
                let not_bad = self.terms.mk_not(bad_at_i);
                conjuncts.push(not_bad);
            }
        }

        // Trans(sᵢ, sᵢ₊₁) for i = 0 .. k-1.
        // As in the base case, the transition relation is the DISJUNCTION of the
        // matching rules – conjoining nondeterministic rules would make the step
        // formula spuriously UNSAT and produce an unsound k-inductive "proof".
        for i in 0..k {
            let mut disjuncts: Vec<TermId> = Vec::new();
            for rule in self.system.rules_by_head(pred_id) {
                if rule.body.predicates.is_empty() {
                    continue; // skip init rules
                }
                if rule.body.predicates.iter().any(|a| a.pred != pred_id) {
                    continue;
                }
                if let (Some(body_app), RuleHead::Predicate(head_app)) =
                    (rule.body.predicates.first(), &rule.head)
                {
                    let mut subst = subst_from_args(&body_app.args, &step_vars[i as usize]);
                    subst.extend(subst_from_args(&head_app.args, &step_vars[i as usize + 1]));
                    let trans_c = self.terms.substitute(rule.body.constraint, &subst);
                    disjuncts.push(trans_c);
                }
            }
            if !disjuncts.is_empty() {
                let step_trans = self.terms.mk_or(disjuncts);
                conjuncts.push(step_trans);
            }
        }

        // Bad(sₖ)  – the property violation at the final step
        for (args, bad_constraint) in &bad_templates {
            let subst = subst_from_args(args, &step_vars[k as usize]);
            let bad_at_k = self.terms.substitute(*bad_constraint, &subst);
            conjuncts.push(bad_at_k);
        }

        if conjuncts.is_empty() {
            // Nothing to check – conservatively unknown
            return Ok(BmcResult::Unknown);
        }

        let formula = self.terms.mk_and(conjuncts);
        self.stats.num_smt_queries = self.stats.num_smt_queries.saturating_add(1);

        let mut smt = SmtSolver::new(self.terms, self.system);
        smt.push();
        smt.assert(formula);
        let sat_result = smt.check_sat();
        smt.pop();

        match sat_result {
            Ok(false) => {
                // UNSAT: the inductive step holds – k-induction proves safety
                debug!("K-induction: proved safety with k={}", k);
                Ok(BmcResult::Safe(k))
            }
            Ok(true) => {
                // SAT: k-induction failed at this k (but NOT an Unsafe result –
                // SAT here only means we cannot prove safety with k steps)
                trace!("K-induction: step formula SAT at k={}, inconclusive", k);
                Ok(BmcResult::Unknown)
            }
            Err(SmtError::Unknown) => Ok(BmcResult::Unknown),
            Err(e) => Err(BmcError::Smt(e)),
        }
    }

    /// Get the statistics
    pub fn stats(&self) -> &BmcStats {
        &self.stats
    }

    /// Get the counterexample (if found)
    pub fn counterexample(&self) -> Option<&Counterexample> {
        self.counterexample.as_ref()
    }
}

// ========  ========
// Counterexample extraction
// ========  ========

/// Build a `Counterexample` by evaluating the per-step state variables in the
/// current SAT model held inside `smt`.
fn build_counterexample_from_model(
    smt: &mut SmtSolver<'_>,
    pred_id: PredId,
    step_vars: &[Vec<TermId>],
    k: u32,
) -> Counterexample {
    let mut cex = Counterexample::new();

    for step in 0..=k {
        let vars = &step_vars[step as usize];
        let assignments: SmallVec<[(TermId, TermId); 4]> = vars
            .iter()
            .copied()
            .filter_map(|var| smt.eval_in_model(var).map(|val| (var, val)))
            .collect();

        cex.push(CexState {
            pred: pred_id,
            state: vars.first().copied().unwrap_or(TermId::new(0)),
            rule: None,
            assignments,
        });
    }

    cex
}

// ========  ========
// Hybrid BMC + PDR solver
// ========  ========

/// Hybrid BMC + PDR solver
///
/// Runs BMC and PDR in parallel (or sequentially) and returns
/// the first result.
pub struct HybridSolver {
    /// BMC configuration
    pub bmc_config: BmcConfig,
    /// Run BMC first before PDR
    pub bmc_first: bool,
}

impl HybridSolver {
    /// Create a new hybrid solver
    pub fn new() -> Self {
        Self {
            bmc_config: BmcConfig::default(),
            bmc_first: true,
        }
    }

    /// Run BMC first with shallow depth to quickly find bugs
    pub fn quick_bmc(mut self) -> Self {
        self.bmc_config.max_depth = 10;
        self.bmc_first = true;
        self
    }
}

impl Default for HybridSolver {
    fn default() -> Self {
        Self::new()
    }
}

// ========  ========
// Tests
// ========  ========

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chc::{ChcSystem, PredicateApp};

    #[test]
    fn test_bmc_creation() {
        let mut terms = TermManager::new();
        let system = ChcSystem::new();
        let bmc = Bmc::new(&mut terms, &system);
        assert_eq!(bmc.stats.max_depth_reached, 0);
    }

    #[test]
    fn test_bmc_config() {
        let config = BmcConfig {
            max_depth: 50,
            use_kinduction: true,
            verbosity: 1,
        };
        assert_eq!(config.max_depth, 50);
        assert!(config.use_kinduction);
    }

    /// Safe system: x=0 initially, x < 0 is the bad state.
    /// Since x starts at 0 and the bad state is x < 0, no counterexample exists.
    #[test]
    fn test_bmc_simple_safe() {
        let mut terms = TermManager::new();
        let mut system = ChcSystem::new();

        let inv = system.declare_predicate("Inv", [terms.sorts.int_sort]);
        let x = terms.mk_var("x", terms.sorts.int_sort);
        let zero = terms.mk_int(0);
        let init_constraint = terms.mk_eq(x, zero);

        system.add_init_rule(
            [("x".to_string(), terms.sorts.int_sort)],
            init_constraint,
            inv,
            [x],
        );

        let neg_constraint = terms.mk_lt(x, zero);
        system.add_query(
            [("x".to_string(), terms.sorts.int_sort)],
            [PredicateApp::new(inv, [x])],
            neg_constraint,
        );

        let config = BmcConfig {
            max_depth: 5,
            use_kinduction: false,
            verbosity: 0,
        };
        let mut bmc = Bmc::with_config(&mut terms, &system, config);
        let result = bmc.check();

        assert!(result.is_ok(), "BMC should not error: {:?}", result);
        match result.expect("BMC result") {
            BmcResult::Safe(_) | BmcResult::Unknown => {}
            BmcResult::Unsafe(_) => panic!("Expected safe or unknown result"),
        }
    }

    /// Unsafe system: x=0 initially, bad state is x=0.
    /// Should find counterexample at depth 0.
    #[test]
    fn test_bmc_unsafe_depth0() {
        let mut terms = TermManager::new();
        let mut system = ChcSystem::new();

        let inv = system.declare_predicate("InvU0", [terms.sorts.int_sort]);
        let x = terms.mk_var("xu0", terms.sorts.int_sort);
        let zero = terms.mk_int(0);
        let init_c = terms.mk_eq(x, zero);

        system.add_init_rule(
            [("xu0".to_string(), terms.sorts.int_sort)],
            init_c,
            inv,
            [x],
        );

        // Bad: x = 0  (immediately reachable)
        let bad_c = terms.mk_eq(x, zero);
        system.add_query(
            [("xu0".to_string(), terms.sorts.int_sort)],
            [PredicateApp::new(inv, [x])],
            bad_c,
        );

        let config = BmcConfig {
            max_depth: 5,
            use_kinduction: false,
            verbosity: 0,
        };
        let mut bmc = Bmc::with_config(&mut terms, &system, config);
        let result = bmc.check().expect("BMC should not error");
        assert!(
            matches!(result, BmcResult::Unsafe(0)),
            "Expected Unsafe(0), got {:?}",
            result
        );
    }

    /// Unsafe system: x=0, x'=x+1, bad x=3.  Should find cex at depth 3.
    #[test]
    fn test_bmc_unsafe_depth3() {
        let mut terms = TermManager::new();
        let mut system = ChcSystem::new();

        let inv = system.declare_predicate("InvD3", [terms.sorts.int_sort]);
        let x = terms.mk_var("xd3", terms.sorts.int_sort);
        let xp = terms.mk_var("xd3_next", terms.sorts.int_sort);
        let zero = terms.mk_int(0);
        let one = terms.mk_int(1);
        let three = terms.mk_int(3);

        // Init: x = 0
        let init_c = terms.mk_eq(x, zero);
        system.add_init_rule(
            [("xd3".to_string(), terms.sorts.int_sort)],
            init_c,
            inv,
            [x],
        );

        // Trans: x' = x + 1
        let x_plus_1 = terms.mk_add([x, one]);
        let trans_c = terms.mk_eq(xp, x_plus_1);
        system.add_transition_rule(
            [
                ("xd3".to_string(), terms.sorts.int_sort),
                ("xd3_next".to_string(), terms.sorts.int_sort),
            ],
            [PredicateApp::new(inv, [x])],
            trans_c,
            inv,
            [xp],
        );

        // Bad: x = 3
        let bad_c = terms.mk_eq(x, three);
        system.add_query(
            [("xd3".to_string(), terms.sorts.int_sort)],
            [PredicateApp::new(inv, [x])],
            bad_c,
        );

        let config = BmcConfig {
            max_depth: 5,
            use_kinduction: false,
            verbosity: 0,
        };
        let mut bmc = Bmc::with_config(&mut terms, &system, config);
        let result = bmc.check().expect("BMC should not error");
        assert!(
            matches!(result, BmcResult::Unsafe(3)),
            "Expected Unsafe(3), got {:?}",
            result
        );
        // Counterexample should be present
        assert!(bmc.counterexample().is_some());
    }

    /// 1-inductive safe system: Init: x=0, Trans: x'=x+1, Bad: x<0.
    /// k-induction with k=1 should prove Safe.
    #[test]
    fn test_kinduction_safe_1ind() {
        let mut terms = TermManager::new();
        let mut system = ChcSystem::new();

        let inv = system.declare_predicate("InvK1", [terms.sorts.int_sort]);
        let x = terms.mk_var("xk1", terms.sorts.int_sort);
        let xp = terms.mk_var("xk1_next", terms.sorts.int_sort);
        let zero = terms.mk_int(0);
        let one = terms.mk_int(1);

        // Init: x = 0
        let init_c = terms.mk_eq(x, zero);
        system.add_init_rule(
            [("xk1".to_string(), terms.sorts.int_sort)],
            init_c,
            inv,
            [x],
        );

        // Trans: x' = x + 1
        let x_plus_1 = terms.mk_add([x, one]);
        let trans_c = terms.mk_eq(xp, x_plus_1);
        system.add_transition_rule(
            [
                ("xk1".to_string(), terms.sorts.int_sort),
                ("xk1_next".to_string(), terms.sorts.int_sort),
            ],
            [PredicateApp::new(inv, [x])],
            trans_c,
            inv,
            [xp],
        );

        // Bad: x < 0
        let bad_c = terms.mk_lt(x, zero);
        system.add_query(
            [("xk1".to_string(), terms.sorts.int_sort)],
            [PredicateApp::new(inv, [x])],
            bad_c,
        );

        let result = Bmc::new(&mut terms, &system)
            .check_kinduction(1)
            .expect("k-induction should not error");
        // x starts at 0 and only increases; x < 0 is unreachable.
        // k=1 induction: base case is UNSAT, step formula checks:
        //   ¬(x<0) ∧ x'=x+1 ∧ x'<0  – UNSAT (x'=x+1 with x≥0 → x'≥1 > 0)
        assert!(
            matches!(result, BmcResult::Safe(1) | BmcResult::Unknown),
            "Expected Safe(1) or Unknown, got {:?}",
            result
        );
    }

    #[test]
    fn test_hybrid_solver_creation() {
        let hybrid = HybridSolver::new();
        assert!(hybrid.bmc_first);

        let quick = HybridSolver::new().quick_bmc();
        assert_eq!(quick.bmc_config.max_depth, 10);
    }
}
