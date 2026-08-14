//! Optimization module for OxiZ Solver
//!
//! Provides SMT optimization features including:
//! - Objective minimization and maximization
//! - Lexicographic optimization (multiple objectives with priorities)
//! - Pareto optimization (multi-objective)
//! - Soft constraints (MaxSMT)

#[allow(unused_imports)]
use crate::prelude::*;
use crate::solver::Model;
use crate::solver::{Solver, SolverResult};
use num_bigint::BigInt;
use num_rational::Rational64;
use num_traits::ToPrimitive;
use oxiz_core::ast::{TermId, TermKind, TermManager};

/// Outcome of a bounded feasibility probe for an integer objective.
enum IntProbe {
    /// A feasible model was found; carries the attained objective value.
    Sat(BigInt, Model),
    /// The bound is infeasible.
    Unsat,
    /// The solver could not decide (incomplete/timeout/non-concrete value).
    Unknown,
}

/// Outcome of a bounded feasibility probe for a real (rational) objective.
enum RealProbe {
    /// A feasible model was found; carries the attained objective value.
    Sat(Rational64, Model),
    /// The bound is infeasible.
    Unsat,
    /// The solver could not decide (incomplete/timeout/non-concrete value).
    Unknown,
}

/// Outcome of the initial feasibility check for an integer objective.
enum InitInt {
    /// Feasible with a concrete integer objective value.
    Sat { value: BigInt, model: Model },
    /// Feasible but the objective is not a concrete integer in the model.
    Symbolic { value: TermId, model: Model },
    /// The base problem is infeasible.
    Unsat,
    /// The solver could not decide.
    Unknown,
}

/// Exponential-probe magnitude cap, as a power of two.
///
/// `2^62` is safely inside the range the `i64`-backed LIA/LRA simplex
/// (`Rational64` numerator/denominator, see `oxiz-theories`'s
/// `arithmetic::simplex`) can represent without overflow: `i64::MAX` is just
/// under `2^63`, so this leaves a factor of two of headroom for the checked
/// intermediate arithmetic the simplex performs during pivoting. Overflow
/// there is itself guarded (it yields a probe `Unknown`, never a silently
/// wrong answer), so this bound is a throughput/completeness trade-off, not a
/// soundness one: an objective whose true optimum lies beyond `2^62` in
/// magnitude is still (honestly documented) misreported `Unbounded`, but that
/// is astronomically higher than the fixed `2^40` cap this replaces.
const MAX_MAGNITUDE_EXP: u32 = 62;

/// Floor of `x / 2` (correct for negative operands, unlike truncating division).
fn floor_half(x: BigInt) -> BigInt {
    let two = BigInt::from(2);
    let q = &x / &two;
    let r = x - &q * &two;
    if r.sign() == num_bigint::Sign::Minus {
        q - BigInt::from(1)
    } else {
        q
    }
}

/// Optimization objective type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObjectiveKind {
    /// Minimize the objective
    Minimize,
    /// Maximize the objective
    Maximize,
}

/// An optimization objective
#[derive(Debug, Clone)]
pub struct Objective {
    /// The term to optimize (must be Int or Real)
    pub term: TermId,
    /// Whether to minimize or maximize
    pub kind: ObjectiveKind,
    /// Priority for lexicographic optimization (lower = higher priority)
    pub priority: usize,
}

/// Result of optimization
#[derive(Debug, Clone)]
pub enum OptimizationResult {
    /// Optimal value found
    Optimal {
        /// The optimal value (as a term)
        value: TermId,
        /// The model achieving this value
        model: crate::solver::Model,
    },
    /// Unbounded (no finite optimum)
    Unbounded,
    /// Unsatisfiable (no solution exists)
    Unsat,
    /// Unknown (timeout, incomplete, etc.)
    Unknown,
}

/// Optimizer for SMT formulas with objectives
///
/// The optimizer extends the basic SMT solver with optimization capabilities,
/// allowing you to minimize or maximize objectives subject to constraints.
///
/// # Examples
///
/// ## Basic Minimization
///
/// ```
/// use oxiz_solver::{Optimizer, OptimizationResult};
/// use oxiz_core::ast::TermManager;
/// use num_bigint::BigInt;
///
/// let mut opt = Optimizer::new();
/// let mut tm = TermManager::new();
///
/// opt.set_logic("QF_LIA");
///
/// let x = tm.mk_var("x", tm.sorts.int_sort);
/// let five = tm.mk_int(BigInt::from(5));
/// opt.assert(tm.mk_ge(x, five));
///
/// // Minimize x (should be 5)
/// opt.minimize(x);
/// let result = opt.optimize(&mut tm);
///
/// match result {
///     OptimizationResult::Optimal { .. } => println!("Found optimal solution"),
///     _ => println!("No optimal solution"),
/// }
/// ```
///
/// ## Lexicographic Optimization
///
/// ```
/// use oxiz_solver::{Optimizer, OptimizationResult};
/// use oxiz_core::ast::TermManager;
/// use num_bigint::BigInt;
///
/// let mut opt = Optimizer::new();
/// let mut tm = TermManager::new();
///
/// opt.set_logic("QF_LIA");
///
/// let x = tm.mk_var("x", tm.sorts.int_sort);
/// let y = tm.mk_var("y", tm.sorts.int_sort);
/// let zero = tm.mk_int(BigInt::from(0));
/// let ten = tm.mk_int(BigInt::from(10));
///
/// opt.assert(tm.mk_ge(x, zero));
/// let zero_y = tm.mk_int(BigInt::from(0));
/// opt.assert(tm.mk_ge(y, zero_y));
/// let sum = tm.mk_add(vec![x, y]);
/// opt.assert(tm.mk_ge(sum, ten));
///
/// // Minimize x first, then y
/// opt.minimize(x);
/// opt.minimize(y);
///
/// let _result = opt.optimize(&mut tm);
/// ```
#[derive(Debug)]
pub struct Optimizer {
    /// The underlying solver (retained for the incremental `push`/`pop` API).
    solver: Solver,
    /// Optimization objectives
    objectives: Vec<Objective>,
    /// Hard assertions. These are *persisted* (never cleared): every call to
    /// [`Optimizer::optimize`] / [`Optimizer::pareto_optimize`] rebuilds a fresh
    /// solver from this list, so the optimizer is fully reusable and no state
    /// leaks between calls.
    assertions: Vec<TermId>,
    /// Logic passed to [`Optimizer::set_logic`], replayed onto each fresh solver.
    logic: Option<String>,
}

impl Optimizer {
    /// Create a new optimizer
    #[must_use]
    pub fn new() -> Self {
        Self {
            solver: Solver::new(),
            objectives: Vec::new(),
            assertions: Vec::new(),
            logic: None,
        }
    }

    /// Add an assertion
    pub fn assert(&mut self, term: TermId) {
        self.assertions.push(term);
    }

    /// Build a fresh solver seeded with the persisted logic, all hard
    /// assertions, and any extra call-scoped constraints.
    ///
    /// Every feasibility query rebuilds from scratch instead of relying on
    /// `push`/`pop`, so an objective fixed during lexicographic optimization (or
    /// a blocking clause during Pareto enumeration) never leaks into a later
    /// query and the optimizer stays sound across repeated use.
    fn build_solver(&self, extra: &[TermId], term_manager: &mut TermManager) -> Solver {
        let mut solver = Solver::new();
        if let Some(logic) = &self.logic {
            solver.set_logic(logic);
        }
        for &assertion in &self.assertions {
            solver.assert(assertion, term_manager);
        }
        for &constraint in extra {
            solver.assert(constraint, term_manager);
        }
        solver
    }

    /// Add a minimization objective
    pub fn minimize(&mut self, term: TermId) {
        self.objectives.push(Objective {
            term,
            kind: ObjectiveKind::Minimize,
            priority: self.objectives.len(),
        });
    }

    /// Add a maximization objective
    pub fn maximize(&mut self, term: TermId) {
        self.objectives.push(Objective {
            term,
            kind: ObjectiveKind::Maximize,
            priority: self.objectives.len(),
        });
    }

    /// Set logic
    pub fn set_logic(&mut self, logic: &str) {
        self.logic = Some(logic.to_string());
        self.solver.set_logic(logic);
    }

    /// Push a scope
    pub fn push(&mut self) {
        self.solver.push();
    }

    /// Pop a scope
    pub fn pop(&mut self) {
        self.solver.pop();
    }

    /// Check satisfiability and optimize objectives.
    ///
    /// Integer objectives are optimized by bounded binary search (with an
    /// unbounded-direction probe); real objectives by an unbounded probe plus
    /// strict-improvement search. Objectives are processed in priority order for
    /// lexicographic optimization: after each objective is optimized it is fixed
    /// to its optimal value while the next is optimized.
    ///
    /// Every feasibility query is run on a **fresh** solver rebuilt from the
    /// persisted hard assertions plus the currently-fixed objectives, so the
    /// optimizer never relies on incremental `pop` to undo a temporary constraint
    /// and is fully reusable: asserting more facts and calling `optimize` again
    /// always reflects exactly the accumulated assertions.
    pub fn optimize(&mut self, term_manager: &mut TermManager) -> OptimizationResult {
        if self.objectives.is_empty() {
            // No objectives were registered: this degenerates to a plain
            // satisfiability check. There is no objective to report an
            // optimum for, so `Optimal::value` cannot carry a real answer.
            // Fabricating a numeric constant here (the previous behavior used
            // `IntConst(0)`) would be indistinguishable from a genuine
            // optimum of `0` -- exactly the silent-incompleteness pattern
            // this crate refuses to produce elsewhere.
            //
            // `OptimizationResult` is a public enum matched exhaustively by
            // several downstream crates (`oxiz-py`, `oxiz-wasm`,
            // `z3_compat_ext`), so adding a dedicated "no objective" variant
            // (or changing `value`'s type) is an API migration out of scope
            // for this fix. Until that broader migration happens, use a
            // `Bool` term as the sentinel `value`: no real objective ever
            // produces a `Bool`, so it can never be confused with an actual
            // numeric optimum, and every current caller only inspects
            // `value`'s *presence* (to stringify/print it) or matches on the
            // `OptimizationResult` variant, never on the sentinel's sort.
            let mut solver = self.build_solver(&[], term_manager);
            return match solver.check(term_manager) {
                SolverResult::Sat => match solver.model() {
                    Some(model) => {
                        let sentinel = term_manager.mk_bool(true);
                        OptimizationResult::Optimal {
                            value: sentinel,
                            model: model.clone(),
                        }
                    }
                    None => OptimizationResult::Unknown,
                },
                SolverResult::Unsat => OptimizationResult::Unsat,
                SolverResult::Unknown => OptimizationResult::Unknown,
            };
        }

        // Sort objectives by priority for lexicographic optimization.
        let mut sorted_objectives = self.objectives.clone();
        sorted_objectives.sort_by_key(|obj| obj.priority);
        let last = sorted_objectives.len() - 1;

        // Constraints fixing already-optimized objectives to their optima. Held
        // in a plain vector and threaded into each fresh solver, so nothing has
        // to be popped and no state can leak into a later call.
        let mut fixed: Vec<TermId> = Vec::new();

        for (idx, objective) in sorted_objectives.iter().enumerate() {
            match self.optimize_single(objective, &fixed, term_manager) {
                OptimizationResult::Optimal { value, model } => {
                    if idx == last {
                        return OptimizationResult::Optimal { value, model };
                    }
                    // Fix this objective to its optimum for the remaining ones.
                    let eq = term_manager.mk_eq(objective.term, value);
                    fixed.push(eq);
                }
                other => return other,
            }
        }

        // Unreachable in practice: the loop above always returns once
        // `idx == last`, and `sorted_objectives` is non-empty in this branch
        // (the empty case returns earlier), so `last` is always visited. Kept
        // as an honest `Unknown` fallback rather than `unreachable!()` so a
        // future refactor that breaks that invariant fails soft, not by
        // panicking.
        OptimizationResult::Unknown
    }

    /// Optimize a single objective, given constraints (`extra`) that fix any
    /// higher-priority objectives already solved in this lexicographic pass.
    fn optimize_single(
        &mut self,
        objective: &Objective,
        extra: &[TermId],
        term_manager: &mut TermManager,
    ) -> OptimizationResult {
        // Determine the objective sort (needs only the term manager).
        let is_int = term_manager
            .get(objective.term)
            .is_some_and(|t| t.sort == term_manager.sorts.int_sort);

        if is_int {
            self.optimize_int(objective, extra, term_manager)
        } else {
            self.optimize_real(objective, extra, term_manager)
        }
    }

    /// Probe feasibility of an integer objective against a bound on a fresh
    /// solver (base assertions + `extra` + the bound constraint).
    ///
    /// Asserts `objective <= bound` (minimization) or `objective >= bound`
    /// (maximization), checks satisfiability, and extracts the attained objective
    /// value from the model. No `push`/`pop` is used, so the query is immune to
    /// incremental-backtracking issues.
    fn probe_int(
        &self,
        objective_term: TermId,
        bound: &BigInt,
        minimize: bool,
        extra: &[TermId],
        term_manager: &mut TermManager,
    ) -> IntProbe {
        let bound_term = term_manager.mk_int(bound.clone());
        let constraint = if minimize {
            term_manager.mk_le(objective_term, bound_term)
        } else {
            term_manager.mk_ge(objective_term, bound_term)
        };
        let mut probe_extra = extra.to_vec();
        probe_extra.push(constraint);
        let mut solver = self.build_solver(&probe_extra, term_manager);

        match solver.check(term_manager) {
            SolverResult::Sat => match solver.model() {
                Some(model) => {
                    let model = model.clone();
                    let value_term = model.eval(objective_term, term_manager);
                    match term_manager.get(value_term).map(|t| t.kind.clone()) {
                        Some(TermKind::IntConst(n)) => IntProbe::Sat(n, model),
                        _ => IntProbe::Unknown,
                    }
                }
                None => IntProbe::Unknown,
            },
            SolverResult::Unsat => IntProbe::Unsat,
            SolverResult::Unknown => IntProbe::Unknown,
        }
    }

    /// Probe feasibility of a real objective against a bound on a fresh solver.
    ///
    /// The comparison is `<`/`>` when `strict`, else `<=`/`>=` (direction chosen
    /// by `minimize`). Returns the attained objective value on success.
    fn probe_real(
        &self,
        objective_term: TermId,
        bound: Rational64,
        minimize: bool,
        strict: bool,
        extra: &[TermId],
        term_manager: &mut TermManager,
    ) -> RealProbe {
        let bound_term = term_manager.mk_real(bound);
        let constraint = match (minimize, strict) {
            (true, false) => term_manager.mk_le(objective_term, bound_term),
            (true, true) => term_manager.mk_lt(objective_term, bound_term),
            (false, false) => term_manager.mk_ge(objective_term, bound_term),
            (false, true) => term_manager.mk_gt(objective_term, bound_term),
        };
        let mut probe_extra = extra.to_vec();
        probe_extra.push(constraint);
        let mut solver = self.build_solver(&probe_extra, term_manager);

        match solver.check(term_manager) {
            SolverResult::Sat => match solver.model() {
                Some(model) => {
                    let model = model.clone();
                    let value_term = model.eval(objective_term, term_manager);
                    match term_manager.get(value_term).map(|t| t.kind.clone()) {
                        Some(TermKind::RealConst(v)) => RealProbe::Sat(v, model),
                        Some(TermKind::IntConst(n)) => match n.to_i64() {
                            Some(i) => RealProbe::Sat(Rational64::from_integer(i), model),
                            None => RealProbe::Unknown,
                        },
                        _ => RealProbe::Unknown,
                    }
                }
                None => RealProbe::Unknown,
            },
            SolverResult::Unsat => RealProbe::Unsat,
            SolverResult::Unknown => RealProbe::Unknown,
        }
    }

    /// Optimize an integer objective by exponential (galloping) probing
    /// followed by binary search.
    ///
    /// 1. **Feasibility** – establish an initial feasible objective value.
    /// 2. **Exponential probe** – starting from a modest magnitude, repeatedly
    ///    double the probed bound in the unbounded direction while the
    ///    objective remains reachable there. This is the standard
    ///    unbounded/galloping-search technique: it finds a bracket
    ///    `(known-infeasible bound, known-feasible value]` for *any* finite
    ///    optimum instead of testing a single fixed magnitude, so a
    ///    genuinely finite optimum is no longer misreported `Unbounded` just
    ///    for exceeding an arbitrary cap.
    /// 3. **Binary search** – bisect the bracket found in step 2 to the exact
    ///    optimum.
    ///
    /// Doubling is capped at [`MAX_MAGNITUDE_EXP`] (see its doc comment for
    /// why that bound is safe against theory-solver overflow). If the
    /// objective is still reachable at every doubled magnitude up to the cap,
    /// no finite bracket exists to bisect and the objective is reported
    /// [`OptimizationResult::Unbounded`] – a documented, honest trade-off
    /// (nothing is ever fabricated), just one pushed astronomically higher
    /// than a naive fixed threshold. Any `Unknown` from a probe propagates as
    /// [`OptimizationResult::Unknown`].
    fn optimize_int(
        &mut self,
        objective: &Objective,
        extra: &[TermId],
        term_manager: &mut TermManager,
    ) -> OptimizationResult {
        let one = BigInt::from(1);

        let minimize = matches!(objective.kind, ObjectiveKind::Minimize);

        // Phase 1: initial feasibility + attained value.
        let (mut best_value, mut best_model) =
            match self.probe_unbounded_int(objective.term, extra, term_manager) {
                InitInt::Unsat => return OptimizationResult::Unsat,
                InitInt::Unknown => return OptimizationResult::Unknown,
                InitInt::Symbolic { value, model } => {
                    // Objective is not a concrete integer in the model; return the
                    // feasible point rather than driving a numeric search.
                    return OptimizationResult::Optimal { value, model };
                }
                InitInt::Sat { value, model } => (value, model),
            };

        // Phase 2: exponential (doubling) probe to find a finite bracket.
        // Starts at 2^10 = 1024: small enough to be cheap when the optimum is
        // nearby, large enough that trivially-bounded problems (the common
        // case) settle in a handful of probes.
        let mut exponent = 10u32;
        let mut magnitude = BigInt::from(1u64) << exponent;
        let infeasible_bound = loop {
            let probe_bound = if minimize {
                -&magnitude
            } else {
                magnitude.clone()
            };
            match self.probe_int(objective.term, &probe_bound, minimize, extra, term_manager) {
                IntProbe::Unknown => return OptimizationResult::Unknown,
                IntProbe::Sat(val, model) => {
                    // Reachable at this magnitude: the true optimum (if
                    // finite) is at least this far out. Record the attained
                    // value as the new known-feasible anchor and double.
                    best_value = val;
                    best_model = model;
                    if exponent >= MAX_MAGNITUDE_EXP {
                        // Exhausted the safe probing range without ever
                        // hitting infeasibility: documented trade-off (see
                        // this function's doc comment).
                        return OptimizationResult::Unbounded;
                    }
                    exponent += 1;
                    magnitude = BigInt::from(1u64) << exponent;
                }
                IntProbe::Unsat => break probe_bound,
            }
        };

        // Phase 3: binary search in the bracket established above, which is
        // now finite and bounded.
        // minimize: optimum in [infeasible_bound + 1, best_value]
        // maximize: optimum in [best_value, infeasible_bound - 1]
        let (mut lo, mut hi) = if minimize {
            (infeasible_bound + &one, best_value.clone())
        } else {
            (best_value.clone(), infeasible_bound - &one)
        };

        let mut guard = 0u32;
        while lo < hi {
            guard += 1;
            if guard > 4096 {
                // Iteration budget exhausted without proving optimality: be
                // honest rather than returning an unverified value. The
                // bracket width is at most `2^MAX_MAGNITUDE_EXP`, so a sound
                // binary search never needs more than ~`MAX_MAGNITUDE_EXP`
                // iterations; this guard only fires on a logic bug, but it
                // must fail honest (`Unknown`) rather than loop forever.
                return OptimizationResult::Unknown;
            }
            let mid = if minimize {
                // floor((lo + hi) / 2), strictly below hi
                floor_half(&lo + &hi)
            } else {
                // ceil((lo + hi) / 2), strictly above lo
                floor_half(&lo + &hi + &one)
            };
            match self.probe_int(objective.term, &mid, minimize, extra, term_manager) {
                IntProbe::Unknown => return OptimizationResult::Unknown,
                IntProbe::Sat(val, model) => {
                    best_model = model;
                    best_value = val.clone();
                    if minimize {
                        hi = val;
                    } else {
                        lo = val;
                    }
                }
                IntProbe::Unsat => {
                    if minimize {
                        lo = &mid + &one;
                    } else {
                        hi = &mid - &one;
                    }
                }
            }
        }

        OptimizationResult::Optimal {
            value: term_manager.mk_int(best_value),
            model: best_model,
        }
    }

    /// Establish initial feasibility for an integer objective and read its
    /// attained value from the model.
    fn probe_unbounded_int(
        &self,
        objective_term: TermId,
        extra: &[TermId],
        term_manager: &mut TermManager,
    ) -> InitInt {
        let mut solver = self.build_solver(extra, term_manager);
        match solver.check(term_manager) {
            SolverResult::Unsat => InitInt::Unsat,
            SolverResult::Unknown => InitInt::Unknown,
            SolverResult::Sat => match solver.model() {
                Some(model) => {
                    let model = model.clone();
                    let value_term = model.eval(objective_term, term_manager);
                    match term_manager.get(value_term).map(|t| t.kind.clone()) {
                        Some(TermKind::IntConst(n)) => InitInt::Sat { value: n, model },
                        _ => InitInt::Symbolic {
                            value: value_term,
                            model,
                        },
                    }
                }
                None => InitInt::Unknown,
            },
        }
    }

    /// Optimize a real (rational) objective.
    ///
    /// Reals cannot be bisected to an exact optimum in general (an infimum may be
    /// open, e.g. `x > 0`), so this uses:
    /// 1. an exponential (doubling) probe to detect unboundedness, and
    /// 2. strict-improvement search: repeatedly demand `objective < best`
    ///    (minimize) / `objective > best` (maximize) on a fresh solver.
    ///
    /// An `Unsat` on the strict-improvement probe proves `best` is the attained
    /// optimum (returned as `Optimal`). If the objective keeps improving without a
    /// proof of optimality within the iteration budget, `Unknown` is returned –
    /// never a fabricated `Optimal`. Integer model values are converted exactly
    /// via [`ToPrimitive::to_i64`]; values that do not fit `i64` (and hence cannot
    /// be represented by [`Rational64`]) yield `Unknown` instead of a silent `0`.
    fn optimize_real(
        &mut self,
        objective: &Objective,
        extra: &[TermId],
        term_manager: &mut TermManager,
    ) -> OptimizationResult {
        let minimize = matches!(objective.kind, ObjectiveKind::Minimize);

        // Phase 1: initial feasibility + attained value.
        let (mut best_value, mut best_model) = {
            let mut solver = self.build_solver(extra, term_manager);
            match solver.check(term_manager) {
                SolverResult::Unsat => return OptimizationResult::Unsat,
                SolverResult::Unknown => return OptimizationResult::Unknown,
                SolverResult::Sat => match solver.model() {
                    Some(model) => {
                        let model = model.clone();
                        let value_term = model.eval(objective.term, term_manager);
                        match term_manager.get(value_term).map(|t| t.kind.clone()) {
                            Some(TermKind::RealConst(v)) => (v, model),
                            Some(TermKind::IntConst(n)) => match n.to_i64() {
                                Some(i) => (Rational64::from_integer(i), model),
                                None => return OptimizationResult::Unknown,
                            },
                            _ => {
                                return OptimizationResult::Optimal {
                                    value: value_term,
                                    model,
                                };
                            }
                        }
                    }
                    None => return OptimizationResult::Unknown,
                },
            }
        };

        // Phase 2: exponential (doubling) unbounded detection, mirroring
        // `optimize_int`'s Phase 2 (see its doc comment for the rationale and
        // for why doubling up to [`MAX_MAGNITUDE_EXP`] is i64-safe). Probing a
        // single fixed magnitude (the previous behavior) misreports any
        // finite optimum beyond that magnitude as `Unbounded`; doubling until
        // infeasibility is hit (or the safe cap is exhausted) instead
        // correctly proceeds to Phase 3 for any finite optimum, however
        // large, while still terminating for genuinely unbounded objectives.
        let mut exponent = 10u32;
        loop {
            let magnitude = Rational64::from_integer(1i64 << exponent);
            let extreme = if minimize { -magnitude } else { magnitude };
            match self.probe_real(
                objective.term,
                extreme,
                minimize,
                false,
                extra,
                term_manager,
            ) {
                RealProbe::Sat(v, model) => {
                    // Reachable at this magnitude: record the attained value
                    // as the new pivot for Phase 3 and double.
                    best_value = v;
                    best_model = model;
                    if exponent >= MAX_MAGNITUDE_EXP {
                        return OptimizationResult::Unbounded;
                    }
                    exponent += 1;
                }
                RealProbe::Unknown => return OptimizationResult::Unknown,
                RealProbe::Unsat => break,
            }
        }

        // Phase 3: strict-improvement search for the exact attained optimum.
        let max_iterations = 1000;
        for _ in 0..max_iterations {
            match self.probe_real(
                objective.term,
                best_value,
                minimize,
                true,
                extra,
                term_manager,
            ) {
                RealProbe::Sat(v, model) => {
                    best_value = v;
                    best_model = model;
                }
                RealProbe::Unsat => {
                    // No strictly-better solution exists – best_value is optimal.
                    return OptimizationResult::Optimal {
                        value: term_manager.mk_real(best_value),
                        model: best_model,
                    };
                }
                RealProbe::Unknown => return OptimizationResult::Unknown,
            }
        }

        // Iteration budget exhausted without proving optimality: be honest.
        OptimizationResult::Unknown
    }
}

impl Default for Optimizer {
    fn default() -> Self {
        Self::new()
    }
}

/// A Pareto-optimal solution (for multi-objective optimization)
#[derive(Debug, Clone)]
pub struct ParetoPoint {
    /// Objective values
    pub values: Vec<TermId>,
    /// Model achieving these values
    pub model: crate::solver::Model,
}

/// Compare two numeric constant terms.
///
/// Returns `None` if either term is not a concrete `Int`/`Real` constant or a
/// large integer cannot be represented for a mixed comparison.
fn numeric_cmp(a: TermId, b: TermId, term_manager: &TermManager) -> Option<core::cmp::Ordering> {
    let ka = term_manager.get(a).map(|t| t.kind.clone())?;
    let kb = term_manager.get(b).map(|t| t.kind.clone())?;
    match (ka, kb) {
        (TermKind::IntConst(x), TermKind::IntConst(y)) => Some(x.cmp(&y)),
        (TermKind::RealConst(x), TermKind::RealConst(y)) => Some(x.cmp(&y)),
        (TermKind::IntConst(x), TermKind::RealConst(y)) => {
            x.to_i64().map(|i| Rational64::from_integer(i).cmp(&y))
        }
        (TermKind::RealConst(x), TermKind::IntConst(y)) => {
            y.to_i64().map(|i| x.cmp(&Rational64::from_integer(i)))
        }
        _ => None,
    }
}

/// Pareto dominance: does point `p` dominate point `q`?
///
/// `p` dominates `q` iff `p` is no worse than `q` in every objective and
/// strictly better in at least one. "Better" is smaller for minimization and
/// larger for maximization. If any objective value pair is incomparable, `p` is
/// conservatively treated as *not* dominating `q`.
fn dominates(
    p: &[TermId],
    q: &[TermId],
    kinds: &[ObjectiveKind],
    term_manager: &TermManager,
) -> bool {
    use core::cmp::Ordering;
    let mut strictly_better = false;
    for i in 0..kinds.len() {
        let Some(ord) = numeric_cmp(p[i], q[i], term_manager) else {
            return false;
        };
        let (no_worse, better) = match kinds[i] {
            ObjectiveKind::Minimize => (ord != Ordering::Greater, ord == Ordering::Less),
            ObjectiveKind::Maximize => (ord != Ordering::Less, ord == Ordering::Greater),
        };
        if !no_worse {
            return false;
        }
        if better {
            strictly_better = true;
        }
    }
    strictly_better
}

impl Optimizer {
    /// Find Pareto-optimal solutions for multi-objective optimization.
    ///
    /// Uses the Guided-Improvement style enumeration:
    /// 1. Find a solution and record it as a candidate Pareto point.
    /// 2. Drop any previously recorded point that the new point dominates, so the
    ///    returned front never contains a dominated point.
    /// 3. Block every solution weakly dominated by the new point (require a strict
    ///    improvement in at least one objective) and repeat until UNSAT.
    ///
    /// Blocking clauses accumulate in a plain vector and are threaded into a fresh
    /// solver each iteration, so no `push`/`pop` is used and the optimizer stays
    /// reusable. Note: this can be expensive for problems with many Pareto points.
    ///
    /// # Honesty note: the returned front is not always exhaustive
    ///
    /// The search stops after `UNSAT` (the front is then genuinely
    /// exhaustive), after `max_points` solutions (a hard iteration cap), or
    /// after `Unknown`/a missing model (the theory solver could not decide).
    /// The return type carries no per-call "exhaustive vs. truncated" flag, so
    /// in the latter two cases the caller receives a valid, non-dominated
    /// front that may nonetheless be *incomplete* – further Pareto points may
    /// exist beyond what was found. This mirrors [`Optimizer::optimize`]'s
    /// documented `Unknown` semantics but, unlike a single-objective query,
    /// cannot itself signal `Unknown` without changing this method's public
    /// return type; nothing about the returned points is ever fabricated.
    pub fn pareto_optimize(&mut self, term_manager: &mut TermManager) -> Vec<ParetoPoint> {
        let mut pareto_front: Vec<ParetoPoint> = Vec::new();

        if self.objectives.is_empty() {
            return pareto_front;
        }

        // Snapshot objective terms/kinds.
        let kinds: Vec<ObjectiveKind> = self.objectives.iter().map(|o| o.kind).collect();
        let obj_terms: Vec<TermId> = self.objectives.iter().map(|o| o.term).collect();

        // Blocking clauses forcing each subsequent solution to strictly improve at
        // least one objective relative to every point found so far.
        let mut blocking: Vec<TermId> = Vec::new();

        // Find Pareto-optimal solutions iteratively.
        let max_points = 100; // Limit to avoid runaway search
        for _ in 0..max_points {
            let mut solver = self.build_solver(&blocking, term_manager);
            match solver.check(term_manager) {
                SolverResult::Sat => {
                    let Some(model) = solver.model() else {
                        // Sat with no model is a solver internal-consistency
                        // gap, not evidence the front is complete: stop
                        // honestly rather than loop or fabricate a point (see
                        // this method's "honesty note" doc comment above).
                        break;
                    };
                    let model = model.clone();

                    // Evaluate all objectives in the model.
                    let mut values = Vec::with_capacity(obj_terms.len());
                    for &term in &obj_terms {
                        values.push(model.eval(term, term_manager));
                    }

                    // Remove any recorded point dominated by the new point.
                    pareto_front.retain(|pt| !dominates(&values, &pt.values, &kinds, term_manager));

                    // Record the new point unless (defensively) it is dominated
                    // by a surviving one.
                    let dominated = pareto_front
                        .iter()
                        .any(|pt| dominates(&pt.values, &values, &kinds, term_manager));
                    if !dominated {
                        pareto_front.push(ParetoPoint {
                            values: values.clone(),
                            model,
                        });
                    }

                    // Block all solutions weakly dominated by this point: a future
                    // solution must strictly improve at least one objective.
                    let mut improvement_disjuncts = Vec::with_capacity(obj_terms.len());
                    for (idx, &term) in obj_terms.iter().enumerate() {
                        let current_value = values[idx];
                        let improvement = match kinds[idx] {
                            ObjectiveKind::Minimize => term_manager.mk_lt(term, current_value),
                            ObjectiveKind::Maximize => term_manager.mk_gt(term, current_value),
                        };
                        improvement_disjuncts.push(improvement);
                    }
                    blocking.push(term_manager.mk_or(improvement_disjuncts));
                }
                // UNSAT after blocking every weakly-dominated solution proves
                // the front is exhaustive: no further Pareto point exists.
                SolverResult::Unsat => break,
                // The theory solver could not decide: stop honestly with
                // whatever front has been established so far rather than
                // guess (see this method's "honesty note" doc comment above)
                // -- the returned front may be incomplete in this case.
                SolverResult::Unknown => break,
            }
        }

        pareto_front
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;
    use num_traits::Zero;

    #[test]
    fn test_solver_direct() {
        // Test the solver directly without optimization
        let mut solver = Solver::new();
        let mut tm = TermManager::new();

        solver.set_logic("QF_LIA");

        let x = tm.mk_var("x", tm.sorts.int_sort);
        let zero = tm.mk_int(BigInt::zero());
        let ten = tm.mk_int(BigInt::from(10));

        let c1 = tm.mk_ge(x, zero);
        let c2 = tm.mk_le(x, ten);

        solver.assert(c1, &mut tm);
        solver.assert(c2, &mut tm);

        let result = solver.check(&mut tm);
        assert_eq!(result, SolverResult::Sat, "Solver should return SAT");
    }

    #[test]
    fn test_optimizer_encoding() {
        // Test that the optimizer properly encodes assertions
        let mut optimizer = Optimizer::new();
        let mut tm = TermManager::new();

        optimizer.set_logic("QF_LIA");

        let x = tm.mk_var("x", tm.sorts.int_sort);
        let zero = tm.mk_int(BigInt::zero());
        let ten = tm.mk_int(BigInt::from(10));

        let c1 = tm.mk_ge(x, zero);
        let c2 = tm.mk_le(x, ten);

        optimizer.assert(c1);
        optimizer.assert(c2);

        // Now encode and check without optimization
        for &assertion in &optimizer.assertions.clone() {
            optimizer.solver.assert(assertion, &mut tm);
        }
        optimizer.assertions.clear();

        let result = optimizer.solver.check(&mut tm);
        assert_eq!(result, SolverResult::Sat, "Should be SAT after encoding");
    }

    #[test]
    fn test_optimizer_basic() {
        let mut optimizer = Optimizer::new();
        let mut tm = TermManager::new();

        optimizer.set_logic("QF_LIA");

        // Create variable x
        let x = tm.mk_var("x", tm.sorts.int_sort);

        // Assert x >= 0
        let zero = tm.mk_int(BigInt::zero());
        let c1 = tm.mk_ge(x, zero);
        optimizer.assert(c1);

        // Assert x <= 10
        let ten = tm.mk_int(BigInt::from(10));
        let c2 = tm.mk_le(x, ten);
        optimizer.assert(c2);

        // Minimize x
        optimizer.minimize(x);

        let result = optimizer.optimize(&mut tm);
        match result {
            OptimizationResult::Optimal { value, .. } => {
                // Should be 0
                if let Some(t) = tm.get(value) {
                    if let TermKind::IntConst(n) = &t.kind {
                        assert_eq!(*n, BigInt::zero());
                    } else {
                        panic!("Expected integer constant");
                    }
                }
            }
            OptimizationResult::Unsat => panic!("Unexpected unsat result"),
            OptimizationResult::Unbounded => panic!("Unexpected unbounded result"),
            OptimizationResult::Unknown => panic!("Got unknown result"),
        }
    }

    #[test]
    fn test_optimizer_maximize() {
        let mut optimizer = Optimizer::new();
        let mut tm = TermManager::new();

        optimizer.set_logic("QF_LIA");

        let x = tm.mk_var("x", tm.sorts.int_sort);

        // Assert x >= 0
        let zero = tm.mk_int(BigInt::zero());
        let c1 = tm.mk_ge(x, zero);
        optimizer.assert(c1);

        // Assert x <= 10
        let ten = tm.mk_int(BigInt::from(10));
        let c2 = tm.mk_le(x, ten);
        optimizer.assert(c2);

        // Maximize x
        optimizer.maximize(x);

        let result = optimizer.optimize(&mut tm);
        match result {
            OptimizationResult::Optimal { value, .. } => {
                // Should be 10
                if let Some(t) = tm.get(value) {
                    if let TermKind::IntConst(n) = &t.kind {
                        assert_eq!(*n, BigInt::from(10));
                    } else {
                        panic!("Expected integer constant");
                    }
                }
            }
            _ => panic!("Expected optimal result"),
        }
    }

    #[test]
    fn test_optimizer_unsat() {
        let mut optimizer = Optimizer::new();
        let mut tm = TermManager::new();

        optimizer.set_logic("QF_LIA");

        // Create unsatisfiable formula using explicit contradiction
        let x = tm.mk_var("x", tm.sorts.int_sort);
        let y = tm.mk_var("y", tm.sorts.int_sort);

        // x = y and x != y (unsatisfiable)
        let eq = tm.mk_eq(x, y);
        let neq = tm.mk_not(eq);
        optimizer.assert(eq);
        optimizer.assert(neq);

        optimizer.minimize(x);

        let result = optimizer.optimize(&mut tm);
        // Audit fix: `x = y AND x != y` is a direct propositional contradiction
        // on the equality atom -- it requires no arithmetic reasoning at all
        // (a CDCL SAT core alone must refute it). The solver now detects this
        // correctly, so accepting `Unknown`/`Optimal` here would silently mask
        // a real regression if theory combination ever dropped the conflict
        // again. Require the honest `Unsat` outright.
        match result {
            OptimizationResult::Unsat => {}
            other => panic!("expected Unsat for `x = y AND x != y`, got {other:?}"),
        }
    }

    // ======== Audit regression tests (solver-p3a) ========

    /// `floor_half` must compute a true floor, including for negative inputs
    /// (truncating integer division would round toward zero and break the
    /// integer binary search in `optimize_int`).
    #[test]
    fn test_floor_half() {
        assert_eq!(floor_half(BigInt::from(4)), BigInt::from(2));
        assert_eq!(floor_half(BigInt::from(5)), BigInt::from(2));
        assert_eq!(floor_half(BigInt::zero()), BigInt::zero());
        assert_eq!(floor_half(BigInt::from(-1)), BigInt::from(-1));
        assert_eq!(floor_half(BigInt::from(-3)), BigInt::from(-2));
        assert_eq!(floor_half(BigInt::from(-4)), BigInt::from(-2));
    }

    /// Numeric comparison and Pareto dominance logic used to filter the front.
    #[test]
    fn test_numeric_cmp_and_dominates() {
        use core::cmp::Ordering;
        let mut tm = TermManager::new();
        let one = tm.mk_int(BigInt::from(1));
        let two = tm.mk_int(BigInt::from(2));
        let two_b = tm.mk_int(BigInt::from(2));

        assert_eq!(numeric_cmp(one, two, &tm), Some(Ordering::Less));
        assert_eq!(numeric_cmp(two, two_b, &tm), Some(Ordering::Equal));
        assert_eq!(numeric_cmp(two, one, &tm), Some(Ordering::Greater));

        let min_kinds = [ObjectiveKind::Minimize, ObjectiveKind::Minimize];
        let p = [one, one];
        let q = [two, two];
        // (1,1) dominates (2,2) when minimizing both.
        assert!(dominates(&p, &q, &min_kinds, &tm));
        assert!(!dominates(&q, &p, &min_kinds, &tm));
        // Equal points do not dominate (no strict improvement).
        assert!(!dominates(&p, &p, &min_kinds, &tm));
        // (1,2) and (2,1) are mutually non-dominated.
        let r = [one, two];
        let s = [two, one];
        assert!(!dominates(&r, &s, &min_kinds, &tm));
        assert!(!dominates(&s, &r, &min_kinds, &tm));

        // Maximization: (2,2) dominates (1,1).
        let max_kinds = [ObjectiveKind::Maximize, ObjectiveKind::Maximize];
        assert!(dominates(&q, &p, &max_kinds, &tm));
        assert!(!dominates(&p, &q, &max_kinds, &tm));
    }

    /// Regression (audit finding: Pareto front contained dominated points).
    /// Whatever solutions are returned, the front must be an antichain – no point
    /// may dominate another. Holds regardless of solver completeness.
    #[test]
    fn test_pareto_front_is_antichain() {
        let mut opt = Optimizer::new();
        let mut tm = TermManager::new();
        opt.set_logic("QF_LIA");

        let x = tm.mk_var("x", tm.sorts.int_sort);
        let y = tm.mk_var("y", tm.sorts.int_sort);
        let zero = tm.mk_int(BigInt::zero());
        let zero_y = tm.mk_int(BigInt::zero());
        let five = tm.mk_int(BigInt::from(5));
        let five_y = tm.mk_int(BigInt::from(5));

        opt.assert(tm.mk_ge(x, zero));
        opt.assert(tm.mk_ge(y, zero_y));
        opt.assert(tm.mk_le(x, five));
        opt.assert(tm.mk_le(y, five_y));
        opt.minimize(x);
        opt.maximize(y);

        let front = opt.pareto_optimize(&mut tm);
        let kinds = [ObjectiveKind::Minimize, ObjectiveKind::Maximize];
        for i in 0..front.len() {
            for j in 0..front.len() {
                if i != j {
                    assert!(
                        !dominates(&front[i].values, &front[j].values, &kinds, &tm),
                        "Pareto front contains a dominated point"
                    );
                }
            }
        }
    }

    /// Regression (audit finding: unbounded objective reported as Optimal with an
    /// arbitrary value). Minimizing an integer with no lower bound must never be
    /// reported as a finite Optimal (nor as Unsat for a feasible problem).
    #[test]
    fn test_unbounded_minimize_not_fabricated() {
        let mut opt = Optimizer::new();
        let mut tm = TermManager::new();
        opt.set_logic("QF_LIA");

        let x = tm.mk_var("x", tm.sorts.int_sort);
        // Only an upper bound; x is unbounded below.
        let hundred = tm.mk_int(BigInt::from(100));
        opt.assert(tm.mk_le(x, hundred));
        opt.minimize(x);

        match opt.optimize(&mut tm) {
            OptimizationResult::Unbounded | OptimizationResult::Unknown => {}
            other => panic!("unbounded minimization reported as {other:?}"),
        }
    }

    /// Regression (audit finding: lexicographic scopes pushed but never popped).
    /// After a two-objective optimize, the optimizer must be reusable: adding a
    /// constraint that only conflicts with a *leaked* fixed-objective equality
    /// must not turn a satisfiable problem spuriously UNSAT.
    #[test]
    fn test_lexicographic_reuse_no_scope_leak() {
        let mut opt = Optimizer::new();
        let mut tm = TermManager::new();
        opt.set_logic("QF_LIA");

        let x = tm.mk_var("x", tm.sorts.int_sort);
        let y = tm.mk_var("y", tm.sorts.int_sort);
        let zero = tm.mk_int(BigInt::zero());
        let zero_y = tm.mk_int(BigInt::zero());
        let ten = tm.mk_int(BigInt::from(10));
        let ten_y = tm.mk_int(BigInt::from(10));

        opt.assert(tm.mk_ge(x, zero));
        opt.assert(tm.mk_ge(y, zero_y));
        opt.assert(tm.mk_le(x, ten));
        opt.assert(tm.mk_le(y, ten_y));
        opt.minimize(x); // optimal x = 0
        opt.minimize(y); // optimal y = 0

        let _ = opt.optimize(&mut tm);

        // Reuse: require x >= 5. If the first call leaked eq(x, 0), this becomes
        // spuriously UNSAT; rebuilding a fresh solver keeps the problem SAT and the
        // last objective (y) still minimizes to 0 under the new constraint.
        let five = tm.mk_int(BigInt::from(5));
        opt.assert(tm.mk_ge(x, five));
        match opt.optimize(&mut tm) {
            OptimizationResult::Optimal { value, .. } => {
                // Returned value is the last objective's optimum: y = 0.
                match tm.get(value).map(|t| t.kind.clone()) {
                    Some(TermKind::IntConst(n)) => {
                        assert_eq!(n, BigInt::zero(), "reuse gave wrong optimum for y");
                    }
                    other => panic!("expected integer optimum, got {other:?}"),
                }
            }
            other => panic!("reuse after lexicographic optimize returned {other:?} (scope leak)"),
        }
    }

    /// Regression: minimizing an integer objective with only an upper bound is
    /// genuinely unbounded below and must be reported `Unbounded` (never a
    /// fabricated finite `Optimal`, never a spurious `Unsat`).
    #[test]
    fn test_unbounded_minimize_reports_unbounded() {
        let mut opt = Optimizer::new();
        let mut tm = TermManager::new();
        opt.set_logic("QF_LIA");
        let x = tm.mk_var("x", tm.sorts.int_sort);
        let hundred = tm.mk_int(BigInt::from(100));
        opt.assert(tm.mk_le(x, hundred));
        opt.minimize(x);
        assert!(
            matches!(opt.optimize(&mut tm), OptimizationResult::Unbounded),
            "unbounded-below integer minimize should report Unbounded"
        );
    }

    /// Regression: maximizing an integer objective with only a lower bound is
    /// unbounded above.
    #[test]
    fn test_unbounded_maximize_reports_unbounded() {
        let mut opt = Optimizer::new();
        let mut tm = TermManager::new();
        opt.set_logic("QF_LIA");
        let x = tm.mk_var("x", tm.sorts.int_sort);
        let zero = tm.mk_int(BigInt::zero());
        opt.assert(tm.mk_ge(x, zero));
        opt.maximize(x);
        assert!(
            matches!(opt.optimize(&mut tm), OptimizationResult::Unbounded),
            "unbounded-above integer maximize should report Unbounded"
        );
    }

    /// A bounded objective near (but within) the unbounded threshold must still be
    /// optimized to its exact value without overflowing the theory solver.
    #[test]
    fn test_bounded_large_optimum_no_overflow() {
        let mut opt = Optimizer::new();
        let mut tm = TermManager::new();
        opt.set_logic("QF_LIA");
        let x = tm.mk_var("x", tm.sorts.int_sort);
        // x in [1_000_000, 2_000_000]; minimize -> 1_000_000.
        let lo = tm.mk_int(BigInt::from(1_000_000));
        let hi = tm.mk_int(BigInt::from(2_000_000));
        opt.assert(tm.mk_ge(x, lo));
        opt.assert(tm.mk_le(x, hi));
        opt.minimize(x);
        match opt.optimize(&mut tm) {
            OptimizationResult::Optimal { value, .. } => {
                match tm.get(value).map(|t| t.kind.clone()) {
                    Some(TermKind::IntConst(n)) => {
                        assert_eq!(n, BigInt::from(1_000_000), "wrong optimum");
                    }
                    other => panic!("expected integer optimum, got {other:?}"),
                }
            }
            other => panic!("expected Optimal, got {other:?}"),
        }
    }
}
