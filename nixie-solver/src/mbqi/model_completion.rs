//! Model Completion Algorithms
//!
//! This module implements model completion for MBQI. Model completion is the process
//! of taking a partial model (which may only define values for some terms) and
//! completing it to a total model that assigns values to all terms.
//!
//! The key challenge is handling function symbols and uninterpreted sorts, which may
//! have infinitely many possible interpretations. We use several strategies:
//!
//! 1. **Macro Solving**: Identify quantifiers that can be solved as macros
//! 2. **Projection Functions**: Map infinite domains to finite representatives
//! 3. **Default Values**: Assign sensible defaults for undefined terms
//! 4. **Finite Universes**: Restrict uninterpreted sorts to finite sets
//!
//! # References
//!
//! - Z3's model_fixer.cpp and q_model_fixer.cpp
//! - "Complete Quantifier Instantiation" (Ge & de Moura, 2009)

#![allow(missing_docs)]

#[allow(unused_imports)]
use crate::prelude::*;
use core::cmp::Ordering;
use core::fmt;
use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::interner::Spur;
use nixie_core::sort::SortId;
use num_bigint::BigInt;
use num_rational::Rational64;
use num_traits::ToPrimitive;
use smallvec::SmallVec;

/// Entry type for function interpretation extraction: (domain_sorts, range_sort, args, result)
type FuncEntry = (SmallVec<[SortId; 4]>, SortId, Vec<TermId>, TermId);

use super::QuantifiedFormula;

/// Maximum number of elements per sort universe (to avoid combinatorial explosion)
const MAX_UNIVERSE_SIZE: usize = 1000;

/// A completed model that assigns values to all relevant terms
#[derive(Debug, Clone)]
pub struct CompletedModel {
    /// Term assignments (term -> value)
    pub assignments: FxHashMap<TermId, TermId>,
    /// Function interpretations
    pub function_interps: FxHashMap<Spur, FunctionInterpretation>,
    /// Universes for uninterpreted sorts (sort -> finite set of values)
    pub universes: FxHashMap<SortId, Vec<TermId>>,
    /// Default values for each sort
    pub defaults: FxHashMap<SortId, TermId>,
    /// Generation number
    pub generation: u32,
}

impl CompletedModel {
    /// Create a new empty completed model
    pub fn new() -> Self {
        Self {
            assignments: FxHashMap::default(),
            function_interps: FxHashMap::default(),
            universes: FxHashMap::default(),
            defaults: FxHashMap::default(),
            generation: 0,
        }
    }

    /// Get the value of a term in this model
    pub fn eval(&self, term: TermId) -> Option<TermId> {
        self.assignments.get(&term).copied()
    }

    /// Set the value of a term
    pub fn set(&mut self, term: TermId, value: TermId) {
        self.assignments.insert(term, value);
    }

    /// Get the universe for a sort
    pub fn universe(&self, sort: SortId) -> Option<&[TermId]> {
        self.universes.get(&sort).map(|v| v.as_slice())
    }

    /// Add a value to a sort's universe
    pub fn add_to_universe(&mut self, sort: SortId, value: TermId) {
        self.universes.entry(sort).or_default().push(value);
    }

    /// Get the default value for a sort
    pub fn default_value(&self, sort: SortId) -> Option<TermId> {
        self.defaults.get(&sort).copied()
    }

    /// Set the default value for a sort
    pub fn set_default(&mut self, sort: SortId, value: TermId) {
        self.defaults.insert(sort, value);
    }

    /// Check if a sort has an uninterpreted universe
    pub fn has_uninterpreted_sort(&self, sort: SortId) -> bool {
        self.universes.contains_key(&sort)
    }

    /// Evaluate a function application f(v1, ..., vn) under this model.
    ///
    /// First evaluates each argument to its model value, then looks up the
    /// function interpretation table. Falls back to else_value or sort default.
    pub fn eval_apply(&self, func: Spur, evaluated_args: &[TermId]) -> Option<TermId> {
        if let Some(interp) = self.function_interps.get(&func) {
            // Try direct lookup with evaluated args
            if let Some(result) = interp.lookup(evaluated_args) {
                return Some(result);
            }
            // Try else_value
            if let Some(else_val) = interp.else_value {
                return Some(else_val);
            }
            // Try default for range sort
            if let Some(default) = self.defaults.get(&interp.range) {
                return Some(*default);
            }
        }
        None
    }

    /// Collect the finite universe for each sort appearing in bound variables
    /// of the given quantifiers, by scanning ground terms in the current model.
    ///
    /// For interpreted sorts (Int, Real, Bool, BV), collects values that actually
    /// appear in the model assignments. For uninterpreted sorts, uses existing
    /// universe or creates one from model values.
    pub fn collect_universes_from_model(
        &mut self,
        quantifiers: &[QuantifiedFormula],
        manager: &TermManager,
    ) {
        // Gather all sorts that appear in bound variables
        let mut needed_sorts: FxHashSet<SortId> = FxHashSet::default();
        for quant in quantifiers {
            for &(_name, sort) in &quant.bound_vars {
                needed_sorts.insert(sort);
            }
        }

        // For each needed sort, build a universe from ground terms in the model
        for sort in needed_sorts {
            // Skip if universe already exists
            if self.universes.contains_key(&sort) {
                continue;
            }

            let mut universe_values: Vec<TermId> = Vec::new();
            let mut seen: FxHashSet<TermId> = FxHashSet::default();

            // Scan all model assignments for values of this sort
            for (&term, &value) in &self.assignments {
                // Check if the term has the right sort
                if let Some(t) = manager.get(term) {
                    if t.sort == sort && seen.insert(value) {
                        universe_values.push(value);
                    }
                }
                // Also check if the value itself has the right sort
                if let Some(v) = manager.get(value) {
                    if v.sort == sort && seen.insert(value) {
                        universe_values.push(value);
                    }
                }
            }

            // Also scan function interpretation entries for values of this sort
            for interp in self.function_interps.values() {
                for entry in &interp.entries {
                    // Check args
                    for (i, &arg) in entry.args.iter().enumerate() {
                        if i < interp.domain.len() && interp.domain[i] == sort && seen.insert(arg) {
                            universe_values.push(arg);
                        }
                    }
                    // Check result
                    if interp.range == sort && seen.insert(entry.result) {
                        universe_values.push(entry.result);
                    }
                }
            }

            // Enforce maximum universe size
            universe_values.truncate(MAX_UNIVERSE_SIZE);

            if !universe_values.is_empty() {
                self.universes.insert(sort, universe_values);
            }
        }
    }

    /// Complete all function interpretations by ensuring they have an else_value.
    ///
    /// For each function f: S1 x ... x Sn -> S that appears in the model:
    ///  - If it has explicit entries but no else_value, set else_value to
    ///    the most common result value (or the sort default).
    ///  - If it has no entries at all, set else_value to the sort default.
    ///
    /// IMPORTANT: For functions with EXPLICIT entries (finite interpretation from
    /// ground assertions), do NOT set else_value.  Using "most common result" as
    /// else_value is unsound: it makes f(v) evaluate to a wrong value when v is
    /// not in the explicit entries, causing MBQI to generate a spurious False
    /// evaluation and add an empty SAT clause.
    ///
    /// Only set else_value for completely uninterpreted functions (no entries).
    pub fn complete_function_interpretations(&mut self) {
        // Collect updates to avoid borrow issues
        let updates: Vec<(Spur, TermId)> = self
            .function_interps
            .iter()
            .filter_map(|(&name, interp)| {
                if interp.else_value.is_some() {
                    return None;
                }
                // If the function has explicit entries, do NOT set an else_value.
                // Setting else_value would make f(v) return a wrong value for
                // unknown v, potentially causing false UNSAT in SAT instances.
                if !interp.entries.is_empty() {
                    return None;
                }
                // For completely uninterpreted functions (no entries), use sort default
                if let Some(&default) = self.defaults.get(&interp.range) {
                    return Some((name, default));
                }
                None
            })
            .collect();

        for (name, else_val) in updates {
            if let Some(interp) = self.function_interps.get_mut(&name) {
                interp.else_value = Some(else_val);
            }
        }
    }
}

impl Default for CompletedModel {
    fn default() -> Self {
        Self::new()
    }
}

/// A function interpretation (finite representation of function mapping)
#[derive(Debug, Clone)]
pub struct FunctionInterpretation {
    /// Function name
    pub name: Spur,
    /// Arity
    pub arity: usize,
    /// Domain sorts
    pub domain: SmallVec<[SortId; 4]>,
    /// Range sort
    pub range: SortId,
    /// Explicit entries (args -> result)
    pub entries: Vec<FunctionEntry>,
    /// Default/else value (for arguments not in entries)
    pub else_value: Option<TermId>,
    /// Projection functions for arguments (if any)
    pub projections: Vec<Option<ProjectionFunctionDef>>,
}

impl FunctionInterpretation {
    /// Create a new function interpretation
    pub fn new(name: Spur, domain: SmallVec<[SortId; 4]>, range: SortId) -> Self {
        let arity = domain.len();
        Self {
            name,
            arity,
            domain,
            range,
            entries: Vec::new(),
            else_value: None,
            projections: vec![None; arity],
        }
    }

    /// Add an entry to the function table
    pub fn add_entry(&mut self, args: Vec<TermId>, result: TermId) {
        if args.len() == self.arity {
            self.entries.push(FunctionEntry { args, result });
        }
    }

    /// Lookup a value in the function table
    pub fn lookup(&self, args: &[TermId]) -> Option<TermId> {
        for entry in &self.entries {
            if entry.args == args {
                return Some(entry.result);
            }
        }
        self.else_value
    }

    /// Check if this is a constant function
    pub fn is_constant(&self) -> bool {
        self.arity == 0
    }

    /// Check if the interpretation is partial (missing else value or entries)
    pub fn is_partial(&self) -> bool {
        self.else_value.is_none() && !self.entries.is_empty()
    }

    /// Get the most common result value
    pub fn max_occurrence_result(&self) -> Option<TermId> {
        if self.entries.is_empty() {
            return None;
        }

        let mut counts: FxHashMap<TermId, usize> = FxHashMap::default();
        for entry in &self.entries {
            *counts.entry(entry.result).or_insert(0) += 1;
        }

        counts
            .into_iter()
            .max_by_key(|(_, count)| *count)
            .map(|(term, _)| term)
    }
}

/// A single entry in a function interpretation
#[derive(Debug, Clone)]
pub struct FunctionEntry {
    /// Arguments
    pub args: Vec<TermId>,
    /// Result value
    pub result: TermId,
}

/// Definition of a projection function for argument position
#[derive(Debug, Clone)]
pub struct ProjectionFunctionDef {
    /// Argument index this projection is for
    pub arg_index: usize,
    /// Sort being projected
    pub sort: SortId,
    /// Sorted values that appear in function applications
    pub values: Vec<TermId>,
    /// Mapping from value to representative term
    pub value_to_term: FxHashMap<TermId, TermId>,
    /// Mapping from term to value
    pub term_to_value: FxHashMap<TermId, TermId>,
}

impl ProjectionFunctionDef {
    /// Create a new projection function definition
    pub fn new(arg_index: usize, sort: SortId) -> Self {
        Self {
            arg_index,
            sort,
            values: Vec::new(),
            value_to_term: FxHashMap::default(),
            term_to_value: FxHashMap::default(),
        }
    }

    /// Add a value to the projection
    pub fn add_value(&mut self, value: TermId, term: TermId) {
        if !self.values.contains(&value) {
            self.values.push(value);
        }
        self.value_to_term.insert(value, term);
        self.term_to_value.insert(term, value);
    }

    /// Project a value to its representative
    pub fn project(&self, value: TermId) -> Option<TermId> {
        self.value_to_term.get(&value).copied()
    }
}

/// Model completer that takes partial models and makes them complete
#[derive(Debug)]
pub struct ModelCompleter {
    /// Macro solver
    macro_solver: MacroSolver,
    /// Model fixer for function interpretations
    model_fixer: ModelFixer,
    /// Handler for uninterpreted sorts
    uninterp_handler: UninterpretedSortHandler,
    /// Cache of completed models
    cache: FxHashMap<u64, CompletedModel>,
    /// Statistics
    stats: CompletionStats,
}

impl ModelCompleter {
    /// Create a new model completer
    pub fn new() -> Self {
        Self {
            macro_solver: MacroSolver::new(),
            model_fixer: ModelFixer::new(),
            uninterp_handler: UninterpretedSortHandler::new(),
            cache: FxHashMap::default(),
            stats: CompletionStats::default(),
        }
    }

    /// Complete a partial model using the Ge & de Moura (2009) approach.
    ///
    /// Steps:
    /// 1. Start from the partial SAT+theory model
    /// 2. Extract function interpretations from Apply terms in the model
    /// 3. Try to solve macro quantifiers (forall x. f(x) = body)
    /// 4. Fix incomplete function interpretations (add else values)
    /// 5. Handle uninterpreted sorts (create finite universes)
    /// 6. Collect universes for all sorts from ground terms in model
    /// 7. Set default values for every sort
    /// 8. Ensure every function has a complete interpretation
    pub fn complete(
        &mut self,
        partial_model: &FxHashMap<TermId, TermId>,
        quantifiers: &[QuantifiedFormula],
        manager: &mut TermManager,
    ) -> Result<CompletedModel, CompletionError> {
        self.stats.num_completions += 1;

        // Start with the partial model
        let mut completed = CompletedModel::new();
        completed.assignments = partial_model.clone();

        // Step 1: Extract function interpretations from Apply terms in the model
        self.extract_function_interpretations(&mut completed, manager);

        // Step 2: Try to solve some quantifiers as macros.
        // Important: do NOT overwrite an existing interpretation extracted in step 1.
        // The partial model's concrete entries (e.g. f(0)=0) are more specific than
        // a macro-derived empty interpretation and must be preserved.
        let macro_results = self.macro_solver.solve_macros(quantifiers, manager)?;
        for (func_name, macro_interp) in macro_results {
            // Only insert the macro interpretation if step 1 found no entries for this function.
            completed
                .function_interps
                .entry(func_name)
                .or_insert(macro_interp);
            // If the function already has entries, the macro definition is redundant
            // for evaluation purposes -- concrete entries are already correct.
        }

        // Step 3: Complete function interpretations (projections, else values)
        self.model_fixer
            .fix_model(&mut completed, quantifiers, manager)?;

        // Step 4: Handle uninterpreted sorts
        self.uninterp_handler
            .complete_universes(&mut completed, manager)?;

        // Step 5: Set default values for all sorts
        self.set_default_values(&mut completed, manager)?;

        // Step 6: Collect universes from ground terms in the model
        // This implements the Ge & de Moura step: for each sort S, build
        // U_S = set of all ground terms of sort S in the current model
        completed.collect_universes_from_model(quantifiers, manager);

        // Step 7: Add default values for sorts that got new universes
        self.set_default_values(&mut completed, manager)?;

        // Step 8: Ensure every function has a complete interpretation
        completed.complete_function_interpretations();

        Ok(completed)
    }

    /// Evaluate an arithmetic expression to a canonical constant TermId.
    ///
    /// This handles simple arithmetic like `Neg(RealConst(r))` → `RealConst(-r)`,
    /// `Neg(IntConst(n))` → `IntConst(-n)`, `Add(...)`, `Sub(...)` etc.
    ///
    /// Returns `None` if the term cannot be reduced to a constant.
    ///
    /// Implemented as an explicit-stack machine with a per-call memo keyed
    /// on `TermId`. The retired native recursion had no visited set, so a
    /// hash-consed DAG whose `Add` operands share subterms was re-evaluated
    /// once per path (exponential on a doubling DAG), and a deep chain
    /// overflowed the call stack. Memoisation is sound because the
    /// evaluation is a pure function of the term, and idempotent on the
    /// manager (`mk_int`/`mk_real` hash-cons). `Neg`/`Sub` still
    /// short-circuit on a non-constant operand exactly as before -- the
    /// right-hand side of a `Sub` whose left side failed is never entered --
    /// while `Add` still folds every operand regardless of earlier failures.
    fn eval_to_const(term: TermId, manager: &mut TermManager) -> Option<TermId> {
        // Accumulator for an Add fold, mirroring the retired recursion's
        // locals exactly.
        struct AddAcc {
            sum_r: Rational64,
            sum_i: BigInt,
            all_real: bool,
            all_int: bool,
        }

        // Resume states. Each variant owns everything needed to continue,
        // so no frame is ever popped in an impossible state.
        enum Frame {
            // Evaluate this term (memo-checked), leaving its result in `last`.
            Enter(TermId),
            // Neg(arg): `last` holds the operand's result.
            NegDone {
                term: TermId,
            },
            // Add: fold `last` (the result of args[next - 1]) into `acc`,
            // then evaluate args[next..].
            AddFold {
                term: TermId,
                args: SmallVec<[TermId; 4]>,
                next: usize,
                acc: AddAcc,
            },
            // Sub: `last` holds the lhs result; rhs not yet evaluated.
            SubLhsDone {
                term: TermId,
                rhs: TermId,
            },
            // Sub: `last` holds the rhs result.
            SubRhsDone {
                term: TermId,
                lhs_const: TermId,
            },
        }

        let mut memo: FxHashMap<TermId, Option<TermId>> = FxHashMap::default();
        // Result of the most recently completed evaluation. Every resume
        // frame is pushed directly beneath the `Enter` of the child whose
        // result it consumes, so `last` always holds that child's result
        // when the resume frame pops.
        let mut last: Option<TermId> = None;
        let mut stack: Vec<Frame> = vec![Frame::Enter(term)];

        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Enter(t_id) => {
                    if let Some(&cached) = memo.get(&t_id) {
                        last = cached;
                        continue;
                    }
                    let Some(t) = manager.get(t_id) else {
                        // A missing term is not a constant.
                        memo.insert(t_id, None);
                        last = None;
                        continue;
                    };
                    match &t.kind {
                        TermKind::IntConst(_) | TermKind::RealConst(_) => {
                            memo.insert(t_id, Some(t_id));
                            last = Some(t_id);
                        }
                        TermKind::Neg(arg) => {
                            let arg = *arg;
                            stack.push(Frame::NegDone { term: t_id });
                            stack.push(Frame::Enter(arg));
                        }
                        TermKind::Add(args) => {
                            let args: SmallVec<[TermId; 4]> = args.clone();
                            let acc = AddAcc {
                                sum_r: Rational64::from_integer(0),
                                sum_i: BigInt::from(0i64),
                                all_real: true,
                                all_int: true,
                            };
                            if let Some(&first) = args.first() {
                                stack.push(Frame::AddFold {
                                    term: t_id,
                                    args,
                                    next: 1,
                                    acc,
                                });
                                stack.push(Frame::Enter(first));
                            } else {
                                // `all_* && !args.is_empty()` can never hold.
                                memo.insert(t_id, None);
                                last = None;
                            }
                        }
                        TermKind::Sub(lhs, rhs) => {
                            let (lhs, rhs) = (*lhs, *rhs);
                            stack.push(Frame::SubLhsDone { term: t_id, rhs });
                            stack.push(Frame::Enter(lhs));
                        }
                        _ => {
                            memo.insert(t_id, None);
                            last = None;
                        }
                    }
                }
                Frame::NegDone { term: t_id } => {
                    let value = match last {
                        Some(inner) => match manager.get(inner).map(|it| it.kind.clone()) {
                            Some(TermKind::IntConst(n)) => {
                                let neg_n = -n;
                                Some(manager.mk_int(neg_n))
                            }
                            Some(TermKind::RealConst(r)) => Some(manager.mk_real(-r)),
                            _ => None,
                        },
                        None => None,
                    };
                    memo.insert(t_id, value);
                    last = value;
                }
                Frame::AddFold {
                    term: t_id,
                    args,
                    next,
                    mut acc,
                } => {
                    // Fold the result of args[next - 1].
                    match last {
                        Some(c) => match manager.get(c).map(|ct| ct.kind.clone()) {
                            Some(TermKind::RealConst(r)) => {
                                acc.sum_r += r;
                                acc.all_int = false;
                            }
                            Some(TermKind::IntConst(n)) => {
                                acc.sum_r += Rational64::from_integer(n.to_i64().unwrap_or(0));
                                acc.sum_i += n;
                                acc.all_real = false;
                            }
                            _ => {
                                acc.all_real = false;
                                acc.all_int = false;
                            }
                        },
                        None => {
                            acc.all_real = false;
                            acc.all_int = false;
                        }
                    }
                    if let Some(&next_arg) = args.get(next) {
                        stack.push(Frame::AddFold {
                            term: t_id,
                            args,
                            next: next + 1,
                            acc,
                        });
                        stack.push(Frame::Enter(next_arg));
                    } else {
                        // All operands folded (`args` is non-empty here).
                        let value = if acc.all_int {
                            Some(manager.mk_int(acc.sum_i))
                        } else if acc.all_real {
                            Some(manager.mk_real(acc.sum_r))
                        } else {
                            None
                        };
                        memo.insert(t_id, value);
                        last = value;
                    }
                }
                Frame::SubLhsDone { term: t_id, rhs } => match last {
                    Some(lhs_const) => {
                        stack.push(Frame::SubRhsDone {
                            term: t_id,
                            lhs_const,
                        });
                        stack.push(Frame::Enter(rhs));
                    }
                    None => {
                        // Short-circuit: the rhs is never evaluated when the
                        // lhs is not a constant (as in the retired recursion).
                        memo.insert(t_id, None);
                        last = None;
                    }
                },
                Frame::SubRhsDone {
                    term: t_id,
                    lhs_const,
                } => {
                    let value = match last {
                        Some(rhs_const) => {
                            let lhs_kind = manager.get(lhs_const).map(|t| t.kind.clone());
                            let rhs_kind = manager.get(rhs_const).map(|t| t.kind.clone());
                            match (lhs_kind, rhs_kind) {
                                (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => {
                                    Some(manager.mk_int(a - b))
                                }
                                (Some(TermKind::RealConst(a)), Some(TermKind::RealConst(b))) => {
                                    Some(manager.mk_real(a - b))
                                }
                                _ => None,
                            }
                        }
                        None => None,
                    };
                    memo.insert(t_id, value);
                    last = value;
                }
            }
        }

        last
    }

    /// Evaluate an argument to its canonical term: first check model.assignments,
    /// then try arithmetic evaluation, otherwise return the term as-is.
    fn eval_arg(term: TermId, model: &CompletedModel, manager: &mut TermManager) -> TermId {
        // Direct model lookup
        if let Some(val) = model.eval(term) {
            return val;
        }
        // Try arithmetic constant evaluation (e.g., Neg(RealConst(r)) → RealConst(-r))
        if let Some(const_val) = Self::eval_to_const(term, manager) {
            return const_val;
        }
        term
    }

    /// Extract function interpretations from Apply terms in the partial model.
    ///
    /// For each term f(t1,...,tn) in the model assignments that has a value,
    /// record the entry (eval(t1),...,eval(tn)) -> value in f's interpretation.
    /// Arguments are normalized to canonical constant forms (e.g., `Neg(RealConst(r))`
    /// becomes `RealConst(-r)`) so that lookups with different representations of
    /// the same value find the correct entry.
    fn extract_function_interpretations(
        &self,
        model: &mut CompletedModel,
        manager: &mut TermManager,
    ) {
        // Collect all Apply terms and their values
        let mut func_entries: FxHashMap<Spur, Vec<FuncEntry>> = FxHashMap::default();

        // Collect Apply entries first (avoid borrow issues with model.assignments)
        let apply_entries: Vec<(TermId, TermId)> = model
            .assignments
            .iter()
            .filter_map(|(&term, &value)| {
                if manager
                    .get(term)
                    .is_some_and(|t| matches!(t.kind, TermKind::Apply { .. }))
                {
                    Some((term, value))
                } else {
                    None
                }
            })
            .collect();

        for (term, value) in apply_entries {
            let Some(t) = manager.get(term).cloned() else {
                continue;
            };
            if let TermKind::Apply { func, args } = &t.kind {
                // Evaluate each argument to a canonical form:
                // - Direct model lookup (preferred)
                // - Arithmetic constant folding (handles Neg(r), Sub(a,b), etc.)
                // - Fall back to the original term
                let args_cloned: SmallVec<[TermId; 4]> = args.clone();
                let evaluated_args: Vec<TermId> = args_cloned
                    .iter()
                    .map(|&arg| Self::eval_arg(arg, model, manager))
                    .collect();

                let domain: SmallVec<[SortId; 4]> = args
                    .iter()
                    .map(|&arg| manager.get(arg).map_or(manager.sorts.int_sort, |a| a.sort))
                    .collect();

                func_entries.entry(*func).or_default().push((
                    domain,
                    t.sort,
                    evaluated_args,
                    value,
                ));
            }
        }

        // Build function interpretations
        for (func_name, entries) in func_entries {
            match model.function_interps.entry(func_name) {
                std::collections::hash_map::Entry::Occupied(mut occupied) => {
                    // Already have an interpretation; just add entries
                    let interp = occupied.get_mut();
                    for (_domain, _range, args, result) in entries {
                        let already_exists = interp.entries.iter().any(|e| e.args == args);
                        if !already_exists {
                            interp.add_entry(args, result);
                        }
                    }
                }
                std::collections::hash_map::Entry::Vacant(vacant) => {
                    if let Some((domain, range, first_args, first_result)) = entries.first() {
                        // Create new interpretation
                        let mut interp =
                            FunctionInterpretation::new(func_name, domain.clone(), *range);
                        interp.add_entry(first_args.clone(), *first_result);
                        for (_, _, args, result) in entries.iter().skip(1) {
                            let already_exists = interp.entries.iter().any(|e| &e.args == args);
                            if !already_exists {
                                interp.add_entry(args.clone(), *result);
                            }
                        }
                        vacant.insert(interp);
                    }
                }
            }
        }
    }

    /// Set default values for all sorts in the model
    fn set_default_values(
        &mut self,
        model: &mut CompletedModel,
        manager: &mut TermManager,
    ) -> Result<(), CompletionError> {
        // Boolean
        if !model.defaults.contains_key(&manager.sorts.bool_sort) {
            model.set_default(manager.sorts.bool_sort, manager.mk_false());
        }

        // Integer
        if !model.defaults.contains_key(&manager.sorts.int_sort) {
            model.set_default(manager.sorts.int_sort, manager.mk_int(BigInt::from(0)));
        }

        // Real
        if !model.defaults.contains_key(&manager.sorts.real_sort) {
            model.set_default(
                manager.sorts.real_sort,
                manager.mk_real(Rational64::from_integer(0)),
            );
        }

        // Uninterpreted sorts - use first element from universe
        // Collect defaults first to avoid borrow conflict
        let defaults_to_set: Vec<(SortId, TermId)> = model
            .universes
            .iter()
            .filter_map(|(sort, universe)| {
                if !model.defaults.contains_key(sort) {
                    universe.first().map(|&first| (*sort, first))
                } else {
                    None
                }
            })
            .collect();

        for (sort, value) in defaults_to_set {
            model.set_default(sort, value);
        }

        Ok(())
    }

    /// Get completion statistics
    pub fn stats(&self) -> &CompletionStats {
        &self.stats
    }
}

impl Default for ModelCompleter {
    fn default() -> Self {
        Self::new()
    }
}

/// Macro solver that identifies quantifiers that can be solved as macros
///
/// A quantifier can be solved as a macro if it has the form:
/// ∀x. f(x) = body(x)
/// where f is an uninterpreted function and body doesn't contain f
#[derive(Debug)]
pub struct MacroSolver {
    /// Detected macros
    macros: FxHashMap<Spur, MacroDefinition>,
    /// Statistics
    stats: MacroStats,
}

impl MacroSolver {
    /// Create a new macro solver
    pub fn new() -> Self {
        Self {
            macros: FxHashMap::default(),
            stats: MacroStats::default(),
        }
    }

    /// Try to solve quantifiers as macros
    pub fn solve_macros(
        &mut self,
        quantifiers: &[QuantifiedFormula],
        manager: &mut TermManager,
    ) -> Result<FxHashMap<Spur, FunctionInterpretation>, CompletionError> {
        let mut results = FxHashMap::default();

        for quant in quantifiers {
            if let Some(macro_def) = self.try_extract_macro(quant, manager)? {
                self.stats.num_macros_found += 1;
                let interp = self.macro_to_interpretation(&macro_def, manager)?;
                results.insert(macro_def.func_name, interp);
                self.macros.insert(macro_def.func_name, macro_def);
            }
        }

        Ok(results)
    }

    /// Try to extract a macro from a quantified formula
    fn try_extract_macro(
        &self,
        quant: &QuantifiedFormula,
        manager: &TermManager,
    ) -> Result<Option<MacroDefinition>, CompletionError> {
        // Look for pattern: ∀x. f(x) = body(x)
        let Some(body_term) = manager.get(quant.body) else {
            return Ok(None);
        };

        // Check if body is an equality
        if let TermKind::Eq(lhs, rhs) = &body_term.kind {
            // Try both directions
            if let Some(macro_def) = self.try_extract_macro_from_eq(*lhs, *rhs, quant, manager)? {
                return Ok(Some(macro_def));
            }
            if let Some(macro_def) = self.try_extract_macro_from_eq(*rhs, *lhs, quant, manager)? {
                return Ok(Some(macro_def));
            }
        }

        Ok(None)
    }

    /// Try to extract macro from equality lhs = rhs
    fn try_extract_macro_from_eq(
        &self,
        lhs: TermId,
        rhs: TermId,
        quant: &QuantifiedFormula,
        manager: &TermManager,
    ) -> Result<Option<MacroDefinition>, CompletionError> {
        let Some(lhs_term) = manager.get(lhs) else {
            return Ok(None);
        };

        // Check if lhs is f(x1, ..., xn) where f is uninterpreted
        if let TermKind::Apply { func, args } = &lhs_term.kind {
            // Check if all args are bound variables
            let mut is_macro = true;
            for &arg in args.iter() {
                if let Some(arg_term) = manager.get(arg)
                    && !matches!(arg_term.kind, TermKind::Var(_))
                {
                    is_macro = false;
                    break;
                }
            }

            if is_macro {
                // Check if rhs doesn't contain f
                if !self.contains_function(rhs, *func, manager) {
                    return Ok(Some(MacroDefinition {
                        quantifier: quant.term,
                        func_name: *func,
                        bound_vars: quant.bound_vars.clone(),
                        body: rhs,
                    }));
                }
            }
        }

        Ok(None)
    }

    /// Check if term contains an application of `func`.
    ///
    /// Explicit-stack walk with a visited set (existence check, so traversal
    /// order is irrelevant); no input depth can overflow the call stack. The
    /// edge set is every syntactic subterm position, via
    /// [`Self::subterm_positions`] – an occurs-check that misses a position
    /// green-lights an ill-founded macro, so the enumeration must be total.
    fn contains_function(&self, term: TermId, func: Spur, manager: &TermManager) -> bool {
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut work = vec![term];
        while let Some(t_id) = work.pop() {
            if !visited.insert(t_id) {
                continue;
            }

            let Some(t) = manager.get(t_id) else {
                continue;
            };

            if let TermKind::Apply { func: f, .. } = &t.kind
                && *f == func
            {
                return true;
            }
            work.extend(Self::subterm_positions(t_id, manager));
        }
        false
    }

    /// Every immediate subterm position of `term`, for occurs-check purposes.
    ///
    /// Delegates to [`nixie_core::ast::traversal::get_children`], which matches
    /// **exhaustively** over `TermKind` with no catch-all arm: a newly added
    /// term kind is a compile error there rather than a silently childless
    /// node here.  This function used to carry its own 17-kind edge list with a
    /// `_ => vec![]` fallback, so every bit-vector, floating-point, string,
    /// array, `Distinct`, `Xor`, quantifier, `Let`, datatype and `Match` term
    /// looked like a leaf – and [`Self::contains_function`], the occurs-check
    /// that decides whether `forall x. f(x) = rhs` is a safe macro, could miss
    /// an `f` inside `rhs` and install an ill-founded recursive definition as a
    /// function interpretation.
    ///
    /// One position is added on top of the canonical enumeration: quantifier
    /// **patterns** (triggers).  The canonical walk deliberately skips them
    /// (they are instantiation metadata, not semantic children), but an
    /// occurs-check wants *all* syntactic positions – a trigger mentioning `f`
    /// still ties the candidate macro body back to `f`.
    fn subterm_positions(term: TermId, manager: &TermManager) -> SmallVec<[TermId; 4]> {
        let Some(t) = manager.get(term) else {
            return SmallVec::new();
        };
        let mut children = nixie_core::ast::traversal::get_children(&t.kind);
        // Supplement only; the delegation above already covers every semantic
        // child of every kind, so this arm adds positions rather than
        // deciding them.
        match &t.kind {
            TermKind::Forall { patterns, .. } | TermKind::Exists { patterns, .. } => {
                for pattern in patterns {
                    children.extend(pattern.iter().copied());
                }
            }
            _ => {}
        }
        children
    }

    /// Convert a macro definition to a function interpretation.
    ///
    /// For a macro `forall x1:S1 ... xn:Sn. f(x1,...,xn) = body(x1,...,xn)`,
    /// we build an interpretation where the function is defined by the body.
    /// We record the domain sorts from the bound variables and the range sort
    /// from the body, and mark the else_value as None (to be completed later
    /// if needed by model completion).
    fn macro_to_interpretation(
        &self,
        macro_def: &MacroDefinition,
        manager: &mut TermManager,
    ) -> Result<FunctionInterpretation, CompletionError> {
        let func_name = macro_def.func_name;

        // Extract domain sorts from bound variables
        let domain: SmallVec<[SortId; 4]> =
            macro_def.bound_vars.iter().map(|&(_, sort)| sort).collect();

        // Determine range sort from the body term
        let range = manager
            .get(macro_def.body)
            .map_or(manager.sorts.bool_sort, |t| t.sort);

        let interp = FunctionInterpretation::new(func_name, domain, range);
        Ok(interp)
    }

    /// Get statistics
    pub fn stats(&self) -> &MacroStats {
        &self.stats
    }
}

impl Default for MacroSolver {
    fn default() -> Self {
        Self::new()
    }
}

/// A macro definition extracted from a quantifier
#[derive(Debug, Clone)]
pub struct MacroDefinition {
    /// Original quantifier
    pub quantifier: TermId,
    /// Function being defined
    pub func_name: Spur,
    /// Bound variables
    pub bound_vars: SmallVec<[(Spur, SortId); 4]>,
    /// Definition body
    pub body: TermId,
}

/// Model fixer that completes function interpretations
#[derive(Debug)]
pub struct ModelFixer {
    /// Projection functions by sort
    projections: FxHashMap<SortId, Box<dyn ProjectionFunction>>,
    /// Statistics
    stats: FixerStats,
}

impl ModelFixer {
    /// Create a new model fixer
    pub fn new() -> Self {
        Self {
            projections: FxHashMap::default(),
            stats: FixerStats::default(),
        }
    }

    /// Fix a model by completing function interpretations
    pub fn fix_model(
        &mut self,
        model: &mut CompletedModel,
        quantifiers: &[QuantifiedFormula],
        manager: &mut TermManager,
    ) -> Result<(), CompletionError> {
        self.stats.num_fixes += 1;

        // Collect all partial functions from quantifiers
        let partial_functions = self.collect_partial_functions(quantifiers, manager);

        // For each partial function, add projection functions
        // Process one at a time to avoid borrow conflicts
        for func_name in partial_functions.iter() {
            // Check if function exists first (immutable borrow)
            let has_interp = model.function_interps.contains_key(func_name);
            if has_interp {
                // Get mutable reference in separate scope
                if let Some(interp) = model.function_interps.get_mut(func_name) {
                    // Create a minimal projection without full model access
                    // This is a simplified version - full implementation would cache model data
                    for arg_idx in 0..interp.arity {
                        let sort = interp.domain[arg_idx];
                        if self.needs_projection(sort, manager) {
                            // Placeholder: would need model data extracted first
                            interp.projections[arg_idx] = None;
                        }
                    }
                }
            }
        }

        // Do NOT set else_value for partial function interpretations here.
        //
        // Setting else_value to "most common result" is unsound: when a candidate
        // value v is not in the model's finite interpretation of f, using the
        // else_value to evaluate f(v) can produce a wrong (non-model) value that
        // makes a true formula appear as False.  For example, with f(0)=0, f(1)=2,
        // f(3)=7 and forall x y. x<=y => f(x)<=f(y), evaluating at (x=1, y=2) gives
        // f(2) = else_value = 0, making f(1)<=f(2) become 2<=0 = False, which
        // triggers adding an empty SAT clause and returning UNSAT when the formula
        // is actually SAT.
        //
        // Instead, when eval_apply returns None (no direct entry), the caller in
        // evaluate_under_model_cached falls back to rebuilding the term and doing
        // model.eval(new_term).  If not found, it returns the term itself as a
        // symbolic residual.  A symbolic residual in is_counterexample causes MBQI
        // to generate instantiation lemmas that properly constrain f(v), allowing
        // the search to converge without unsound else_value guesses.

        Ok(())
    }

    /// Collect partial function symbols from quantifiers.
    ///
    /// Explicit-stack walk with a visited set shared across all quantifier
    /// bodies. The retired native recursion had **no** visited set at all, so
    /// a hash-consed DAG with shared subterms was re-walked once per path
    /// (exponential on a doubling DAG) and a deep body overflowed the call
    /// stack; the output is a set, so deduplicating visits changes nothing
    /// observable. The descent set (`Apply` args, `Not`/`Neg`, `And`/`Or`,
    /// `Eq`/`Lt`/`Le` sides) is unchanged.
    fn collect_partial_functions(
        &self,
        quantifiers: &[QuantifiedFormula],
        manager: &TermManager,
    ) -> FxHashSet<Spur> {
        let mut functions = FxHashSet::default();
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut work: Vec<TermId> = quantifiers.iter().map(|quant| quant.body).collect();

        while let Some(t_id) = work.pop() {
            if !visited.insert(t_id) {
                continue;
            }

            let Some(t) = manager.get(t_id) else {
                continue;
            };

            if let TermKind::Apply { func, args } = &t.kind {
                // Check if any arg contains variables (not ground)
                let has_vars = args.iter().any(|&arg| {
                    manager
                        .get(arg)
                        .is_some_and(|arg_t| matches!(arg_t.kind, TermKind::Var(_)))
                });

                if has_vars {
                    functions.insert(*func);
                }

                for &arg in args.iter() {
                    work.push(arg);
                }
            }

            match &t.kind {
                TermKind::Not(arg) | TermKind::Neg(arg) => work.push(*arg),
                TermKind::And(args) | TermKind::Or(args) => {
                    for &arg in args.iter() {
                        work.push(arg);
                    }
                }
                TermKind::Eq(lhs, rhs) | TermKind::Lt(lhs, rhs) | TermKind::Le(lhs, rhs) => {
                    work.push(*lhs);
                    work.push(*rhs);
                }
                _ => {}
            }
        }

        functions
    }

    /// Add projection functions for a function interpretation
    fn add_projection_functions(
        &mut self,
        interp: &mut FunctionInterpretation,
        model: &CompletedModel,
        manager: &mut TermManager,
    ) -> Result<(), CompletionError> {
        // For each argument position, create a projection if needed
        for arg_idx in 0..interp.arity {
            let sort = interp.domain[arg_idx];

            // Check if we need a projection for this sort
            if self.needs_projection(sort, manager) {
                let proj_def = self.create_projection(interp, arg_idx, model, manager)?;
                interp.projections[arg_idx] = Some(proj_def);
            }
        }

        Ok(())
    }

    /// Check if a sort needs projection
    fn needs_projection(&self, sort: SortId, manager: &TermManager) -> bool {
        // Arithmetic sorts benefit from projection
        sort == manager.sorts.int_sort || sort == manager.sorts.real_sort
    }

    /// Create a projection function for an argument position
    fn create_projection(
        &mut self,
        interp: &FunctionInterpretation,
        arg_idx: usize,
        model: &CompletedModel,
        manager: &mut TermManager,
    ) -> Result<ProjectionFunctionDef, CompletionError> {
        let sort = interp.domain[arg_idx];
        let mut proj_def = ProjectionFunctionDef::new(arg_idx, sort);

        // Collect all values that appear at this argument position
        for entry in &interp.entries {
            if let Some(&arg_term) = entry.args.get(arg_idx) {
                // Evaluate the argument in the model
                let value = model.eval(arg_term).unwrap_or(arg_term);
                proj_def.add_value(value, arg_term);
            }
        }

        // Sort the values
        proj_def
            .values
            .sort_by(|a, b| self.compare_values(*a, *b, sort, manager));

        Ok(proj_def)
    }

    /// Compare two values for a given sort
    fn compare_values(
        &self,
        a: TermId,
        b: TermId,
        _sort: SortId,
        manager: &TermManager,
    ) -> Ordering {
        let a_term = manager.get(a);
        let b_term = manager.get(b);

        if let (Some(at), Some(bt)) = (a_term, b_term) {
            // Integer comparison
            if let (TermKind::IntConst(av), TermKind::IntConst(bv)) = (&at.kind, &bt.kind) {
                return av.cmp(bv);
            }

            // Real comparison
            if let (TermKind::RealConst(av), TermKind::RealConst(bv)) = (&at.kind, &bt.kind) {
                return av.cmp(bv);
            }

            // Boolean comparison (false < true)
            match (&at.kind, &bt.kind) {
                (TermKind::False, TermKind::True) => return Ordering::Less,
                (TermKind::True, TermKind::False) => return Ordering::Greater,
                (TermKind::False, TermKind::False) | (TermKind::True, TermKind::True) => {
                    return Ordering::Equal;
                }
                _ => {}
            }
        }

        // Fall back to ID comparison
        a.0.cmp(&b.0)
    }

    /// Get statistics
    pub fn stats(&self) -> &FixerStats {
        &self.stats
    }
}

impl Default for ModelFixer {
    fn default() -> Self {
        Self::new()
    }
}

/// Trait for projection functions (maps infinite domain to finite representatives)
pub trait ProjectionFunction: fmt::Debug + Send + Sync {
    /// Compare two values (for sorting)
    fn compare(&self, a: TermId, b: TermId, manager: &TermManager) -> bool;

    /// Create a less-than term
    fn mk_lt(&self, x: TermId, y: TermId, manager: &mut TermManager) -> TermId;
}

/// Arithmetic projection function
#[derive(Debug)]
pub struct ArithmeticProjection {
    /// Whether this is for integers (vs reals)
    is_int: bool,
}

impl ArithmeticProjection {
    pub fn new(is_int: bool) -> Self {
        Self { is_int }
    }
}

impl ProjectionFunction for ArithmeticProjection {
    fn compare(&self, a: TermId, b: TermId, manager: &TermManager) -> bool {
        let a_term = manager.get(a);
        let b_term = manager.get(b);

        if let (Some(at), Some(bt)) = (a_term, b_term) {
            if let (TermKind::IntConst(av), TermKind::IntConst(bv)) = (&at.kind, &bt.kind) {
                return av < bv;
            }
            if let (TermKind::RealConst(av), TermKind::RealConst(bv)) = (&at.kind, &bt.kind) {
                return av < bv;
            }
        }

        a.0 < b.0
    }

    fn mk_lt(&self, x: TermId, y: TermId, manager: &mut TermManager) -> TermId {
        manager.mk_lt(x, y)
    }
}

/// Handler for uninterpreted sorts
#[derive(Debug)]
pub struct UninterpretedSortHandler {
    /// Maximum universe size for each sort
    max_universe_size: usize,
    /// Statistics
    stats: UninterpStats,
}

impl UninterpretedSortHandler {
    /// Create a new handler
    pub fn new() -> Self {
        Self {
            max_universe_size: 8,
            stats: UninterpStats::default(),
        }
    }

    /// Create with custom universe size limit
    pub fn with_max_size(max_size: usize) -> Self {
        let mut handler = Self::new();
        handler.max_universe_size = max_size;
        handler
    }

    /// Complete universes for uninterpreted sorts
    pub fn complete_universes(
        &mut self,
        model: &mut CompletedModel,
        manager: &mut TermManager,
    ) -> Result<(), CompletionError> {
        // Identify uninterpreted sorts
        let uninterp_sorts = self.identify_uninterpreted_sorts(model, manager);

        for sort in uninterp_sorts {
            if let crate::prelude::hash_map::Entry::Vacant(e) = model.universes.entry(sort) {
                // Create a finite universe for this sort
                let universe = self.create_finite_universe(sort, manager)?;
                e.insert(universe);
                self.stats.num_universes_created += 1;
            }
        }

        Ok(())
    }

    /// Identify uninterpreted sorts in the model
    fn identify_uninterpreted_sorts(
        &self,
        model: &CompletedModel,
        manager: &TermManager,
    ) -> Vec<SortId> {
        let mut sorts = Vec::new();

        // Collect sorts from function interpretations
        for interp in model.function_interps.values() {
            for &sort in &interp.domain {
                if self.is_uninterpreted(sort, manager) && !sorts.contains(&sort) {
                    sorts.push(sort);
                }
            }
            if self.is_uninterpreted(interp.range, manager) && !sorts.contains(&interp.range) {
                sorts.push(interp.range);
            }
        }

        sorts
    }

    /// Check if a sort is uninterpreted
    fn is_uninterpreted(&self, sort: SortId, manager: &TermManager) -> bool {
        // A sort is uninterpreted if it's not a built-in sort
        sort != manager.sorts.bool_sort
            && sort != manager.sorts.int_sort
            && sort != manager.sorts.real_sort
    }

    /// Create a finite universe for a sort
    fn create_finite_universe(
        &self,
        sort: SortId,
        manager: &mut TermManager,
    ) -> Result<Vec<TermId>, CompletionError> {
        let mut universe = Vec::new();

        // Create fresh constants for the universe
        for i in 0..self.max_universe_size {
            let name = format!("u!{}", i);
            let const_id = manager.mk_var(&name, sort);
            universe.push(const_id);
        }

        Ok(universe)
    }

    /// Get statistics
    pub fn stats(&self) -> &UninterpStats {
        &self.stats
    }
}

impl Default for UninterpretedSortHandler {
    fn default() -> Self {
        Self::new()
    }
}

/// Error during model completion
#[derive(Debug, Clone)]
pub enum CompletionError {
    /// Could not complete the model
    CompletionFailed(String),
    /// Resource limit exceeded
    ResourceLimit,
    /// Invalid model
    InvalidModel(String),
}

impl fmt::Display for CompletionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CompletionFailed(msg) => write!(f, "Model completion failed: {}", msg),
            Self::ResourceLimit => write!(f, "Resource limit exceeded during completion"),
            Self::InvalidModel(msg) => write!(f, "Invalid model: {}", msg),
        }
    }
}

impl core::error::Error for CompletionError {}

/// Statistics for model completion
#[derive(Debug, Clone, Default)]
pub struct CompletionStats {
    pub num_completions: usize,
    pub num_failures: usize,
}

/// Statistics for macro solving
#[derive(Debug, Clone, Default)]
pub struct MacroStats {
    pub num_macros_found: usize,
    pub num_macros_applied: usize,
}

/// Statistics for model fixing
#[derive(Debug, Clone, Default)]
pub struct FixerStats {
    pub num_fixes: usize,
    pub num_projections_created: usize,
}

/// Statistics for uninterpreted sort handling
#[derive(Debug, Clone, Default)]
pub struct UninterpStats {
    pub num_universes_created: usize,
    pub total_universe_size: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use nixie_core::interner::Key;

    /// Run `f` on a dedicated 128 KiB stack: overflow aborts the process, so
    /// returning at all is part of the assertion.
    ///
    /// This stack and every depth below were scaled down together by a factor
    /// of 8 (from 1 MiB / 100 000).  The pin is the ~10 bytes of stack per
    /// nesting level, not the absolute depth, and the smaller pair keeps the
    /// interned terms out of swap.  Never raise one without the other.
    fn run_on_small_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
        std::thread::Builder::new()
            .stack_size(1 << 17)
            .spawn(f)
            .expect("spawning the constrained-stack test thread should succeed")
            .join()
            .expect("the constrained-stack thread must not panic")
    }

    /// Pin `eval_to_const`'s outputs so the explicit-stack conversion is
    /// proven behavior-preserving, including the deliberately preserved
    /// quirks (mixed Int/Real `Add` folds to `None`).
    #[test]
    fn eval_to_const_pins_semantics() {
        let mut m = TermManager::new();
        let five = m.mk_int(5);
        assert_eq!(ModelCompleter::eval_to_const(five, &mut m), Some(five));

        let neg_five = m.mk_neg(five);
        let minus_five = m.mk_int(-5);
        assert_eq!(
            ModelCompleter::eval_to_const(neg_five, &mut m),
            Some(minus_five)
        );

        let neg_neg_five = m.mk_neg(neg_five);
        assert_eq!(
            ModelCompleter::eval_to_const(neg_neg_five, &mut m),
            Some(five)
        );

        let one = m.mk_int(1);
        let two = m.mk_int(2);
        let three = m.mk_int(3);
        let sum = m.mk_add([one, two, three]);
        let six = m.mk_int(6);
        assert_eq!(ModelCompleter::eval_to_const(sum, &mut m), Some(six));

        let half = m.mk_real(Rational64::new(1, 2));
        let three_halves = m.mk_real(Rational64::new(3, 2));
        let real_sum = m.mk_add([half, three_halves]);
        let expected = m.mk_real(Rational64::from_integer(2));
        assert_eq!(
            ModelCompleter::eval_to_const(real_sum, &mut m),
            Some(expected)
        );

        // Mixed Int/Real Add is not folded (both all_int and all_real drop).
        let mixed = m.mk_add([one, half]);
        assert_eq!(ModelCompleter::eval_to_const(mixed, &mut m), None);

        let x = m.mk_var("x", m.sorts.int_sort);
        let with_var = m.mk_add([one, x]);
        assert_eq!(ModelCompleter::eval_to_const(with_var, &mut m), None);

        let ten = m.mk_int(10);
        let diff = m.mk_sub(ten, three);
        let seven = m.mk_int(7);
        assert_eq!(ModelCompleter::eval_to_const(diff, &mut m), Some(seven));

        // Mixed-sort Sub is not folded.
        let mixed_sub = m.mk_sub(ten, half);
        assert_eq!(ModelCompleter::eval_to_const(mixed_sub, &mut m), None);

        assert_eq!(ModelCompleter::eval_to_const(x, &mut m), None);
    }

    /// A 12 500-deep Sub chain must evaluate on a 128 KiB stack (the retired
    /// recursion overflowed), both when it folds to a constant and when it
    /// short-circuits on a variable leaf.
    #[test]
    fn eval_to_const_survives_deep_chains_on_a_tiny_stack() {
        const DEPTH: usize = 12_500;
        run_on_small_stack(|| {
            let mut m = TermManager::new();
            let one = m.mk_int(1);

            let mut chain = m.mk_int(0);
            for _ in 0..DEPTH {
                chain = m.mk_sub(chain, one);
            }
            let expected = m.mk_int(-(DEPTH as i64));
            assert_eq!(ModelCompleter::eval_to_const(chain, &mut m), Some(expected));

            let x = m.mk_var("x", m.sorts.int_sort);
            let mut var_chain = x;
            for _ in 0..DEPTH {
                var_chain = m.mk_sub(var_chain, one);
            }
            assert_eq!(ModelCompleter::eval_to_const(var_chain, &mut m), None);
        });
    }

    /// A doubling `Add` DAG is exponential without the memo (the retired
    /// recursion re-evaluated both shared operands at every level); with the
    /// memo it must fold essentially instantly, to the exact value.
    #[test]
    fn eval_to_const_memoizes_shared_dags() {
        const LEVELS: usize = 55;
        let mut m = TermManager::new();
        let mut term = m.mk_int(1);
        for _ in 0..LEVELS {
            term = m.mk_add([term, term]);
        }
        let expected = m.mk_int(num_bigint::BigInt::from(1u64) << LEVELS);
        assert_eq!(ModelCompleter::eval_to_const(term, &mut m), Some(expected));
    }

    /// `MacroSolver::contains_function` must walk a 12 500-deep term on a
    /// 128 KiB stack; the "absent" answer requires visiting every node.
    #[test]
    fn contains_function_survives_deep_terms_on_a_tiny_stack() {
        const DEPTH: usize = 12_500;
        run_on_small_stack(|| {
            let mut m = TermManager::new();
            let int_sort = m.sorts.int_sort;
            let x = m.mk_var("x", int_sort);
            let mut chain = x;
            for _ in 0..DEPTH {
                chain = m.mk_apply("f", [chain], int_sort);
            }
            let f = m.intern_str("f");
            let g = m.intern_str("g");
            let solver = MacroSolver::new();
            assert!(solver.contains_function(chain, f, &m));
            assert!(!solver.contains_function(chain, g, &m));
        });
    }

    /// `ModelFixer::collect_partial_functions` must survive a 12 500-deep
    /// quantifier body on a 128 KiB stack, and its new visited set must make
    /// a doubling DAG linear (the retired recursion had no visited set at
    /// all).  `LEVELS` is a doubling count, not a stack depth, so it does not
    /// scale with the thread stack.
    #[test]
    fn collect_partial_functions_survives_depth_and_shared_dags() {
        const DEPTH: usize = 12_500;
        const LEVELS: usize = 55;
        run_on_small_stack(|| {
            let mut m = TermManager::new();
            let int_sort = m.sorts.int_sort;
            let bool_sort = m.sorts.bool_sort;
            let x = m.mk_var("x", int_sort);
            let p_x = m.mk_apply("P", [x], bool_sort);

            let mut chain = p_x;
            for _ in 0..DEPTH {
                chain = m.mk_apply("f", [chain], bool_sort);
            }
            let qf = QuantifiedFormula::new(TermId::new(1), SmallVec::new(), chain, true);
            let fixer = ModelFixer::new();
            let p = m.intern_str("P");
            let functions = fixer.collect_partial_functions(core::slice::from_ref(&qf), &m);
            assert_eq!(functions.len(), 1, "only P is applied to a variable");
            assert!(functions.contains(&p));

            // Doubling DAG: exponential without the visited set.
            let mut dag = p_x;
            for _ in 0..LEVELS {
                dag = m.mk_apply("g", [dag, dag], bool_sort);
            }
            let qf = QuantifiedFormula::new(TermId::new(2), SmallVec::new(), dag, true);
            let functions = fixer.collect_partial_functions(core::slice::from_ref(&qf), &m);
            assert_eq!(functions.len(), 1);
            assert!(functions.contains(&p));
        });
    }

    #[test]
    fn test_completed_model_creation() {
        let model = CompletedModel::new();
        assert_eq!(model.assignments.len(), 0);
        assert_eq!(model.function_interps.len(), 0);
    }

    #[test]
    fn test_completed_model_eval() {
        let mut model = CompletedModel::new();
        let term = TermId::new(1);
        let value = TermId::new(2);

        model.set(term, value);
        assert_eq!(model.eval(term), Some(value));
        assert_eq!(model.eval(TermId::new(99)), None);
    }

    #[test]
    fn test_function_interpretation_lookup() {
        // Create a function with arity 2 (domain has 2 sorts)
        let mut domain = SmallVec::new();
        domain.push(SortId::new(1));
        domain.push(SortId::new(1));

        let mut interp = FunctionInterpretation::new(
            Spur::try_from_usize(1).expect("valid spur"),
            domain,
            SortId::new(1),
        );

        let args = vec![TermId::new(1), TermId::new(2)];
        let result = TermId::new(10);
        interp.add_entry(args.clone(), result);

        assert_eq!(interp.lookup(&args), Some(result));
        assert_eq!(interp.lookup(&[TermId::new(99)]), None);
    }

    #[test]
    fn test_function_interpretation_else_value() {
        let mut interp = FunctionInterpretation::new(
            Spur::try_from_usize(1).expect("valid spur"),
            SmallVec::new(),
            SortId::new(1),
        );

        let else_val = TermId::new(42);
        interp.else_value = Some(else_val);

        assert_eq!(interp.lookup(&[TermId::new(99)]), Some(else_val));
    }

    #[test]
    fn test_function_interpretation_max_occurrence() {
        // Create a function with arity 1 (domain has 1 sort)
        let mut domain = SmallVec::new();
        domain.push(SortId::new(1));

        let mut interp = FunctionInterpretation::new(
            Spur::try_from_usize(1).expect("valid spur"),
            domain,
            SortId::new(1),
        );

        let result1 = TermId::new(10);
        let result2 = TermId::new(20);

        interp.add_entry(vec![TermId::new(1)], result1);
        interp.add_entry(vec![TermId::new(2)], result1);
        interp.add_entry(vec![TermId::new(3)], result2);

        assert_eq!(interp.max_occurrence_result(), Some(result1));
    }

    #[test]
    fn test_projection_function_def() {
        let mut proj = ProjectionFunctionDef::new(0, SortId::new(1));

        let value1 = TermId::new(1);
        let term1 = TermId::new(10);
        proj.add_value(value1, term1);

        assert_eq!(proj.project(value1), Some(term1));
        assert_eq!(proj.values.len(), 1);
    }

    #[test]
    fn test_model_completer_creation() {
        let completer = ModelCompleter::new();
        assert_eq!(completer.stats.num_completions, 0);
    }

    #[test]
    fn test_macro_solver_creation() {
        let solver = MacroSolver::new();
        assert_eq!(solver.stats.num_macros_found, 0);
    }

    #[test]
    fn test_model_fixer_creation() {
        let fixer = ModelFixer::new();
        assert_eq!(fixer.stats.num_fixes, 0);
    }

    #[test]
    fn test_uninterpreted_sort_handler_creation() {
        let handler = UninterpretedSortHandler::new();
        assert_eq!(handler.max_universe_size, 8);
    }

    #[test]
    fn test_uninterpreted_sort_handler_custom_size() {
        let handler = UninterpretedSortHandler::with_max_size(16);
        assert_eq!(handler.max_universe_size, 16);
    }

    #[test]
    fn test_arithmetic_projection() {
        let proj = ArithmeticProjection::new(true);
        assert!(proj.is_int);
    }

    #[test]
    fn test_completion_error_display() {
        let err = CompletionError::CompletionFailed("test".to_string());
        assert!(format!("{}", err).contains("test"));
    }

    // ========  ========
    // Macro occurs-check coverage
    //
    // `MacroSolver::get_children` used to enumerate 17 term kinds and fall
    // through to "no children" for everything else, so `contains_function` --
    // the occurs-check deciding whether `forall x. f(x) = rhs` is a safe macro
    // -- walked straight past every string, array, bit-vector, FP, `Distinct`,
    // `Xor`, quantifier and `Let` node.  An `f` hiding under any of them was
    // invisible and the ill-founded recursive definition was installed as a
    // function interpretation.
    // ========  ========

    /// Build `forall x:sort. f(x) = rhs(f(x))` and ask the macro solver.
    fn macro_from_body(m: &mut TermManager, var_sort: SortId, body: TermId) -> QuantifiedFormula {
        let term = m.mk_forall([("x", var_sort)], body);
        let x_name = m.intern_str("x");
        let mut bound_vars: SmallVec<[(Spur, SortId); 4]> = SmallVec::new();
        bound_vars.push((x_name, var_sort));
        QuantifiedFormula::new(term, bound_vars, body, true)
    }

    /// `forall x:String. f(x) = (str.++ (f x) "a")` is ill-founded: `f` occurs
    /// in the right-hand side under a `StrConcat`.  It must NOT be accepted.
    #[test]
    fn recursive_string_definition_is_not_a_macro() {
        let mut m = TermManager::new();
        let str_sort = m.sorts.string_sort();
        let x = m.mk_var("x", str_sort);
        let f_x = m.mk_apply("f", [x], str_sort);
        let a = m.mk_string_lit("a");
        let rhs = m.mk_str_concat(f_x, a);
        let body = m.mk_eq(f_x, rhs);
        let quant = macro_from_body(&mut m, str_sort, body);

        let f = m.intern_str("f");
        let solver = MacroSolver::new();
        assert!(
            solver.contains_function(rhs, f, &m),
            "the occurs-check must see `f` under `str.++`"
        );

        let mut solver = MacroSolver::new();
        let found = solver
            .solve_macros(core::slice::from_ref(&quant), &mut m)
            .expect("macro solving must not error");
        assert!(
            found.is_empty(),
            "an ill-founded recursive string definition must be rejected as a macro"
        );
    }

    /// `forall x:Int. f(x) = (select (store a x (f x)) x)` is ill-founded:
    /// `f` occurs under `Select`/`Store`, neither of which the old edge list
    /// enumerated.
    #[test]
    fn recursive_array_definition_is_not_a_macro() {
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let array_sort = m.sorts.array(int_sort, int_sort);
        let x = m.mk_var("x", int_sort);
        let f_x = m.mk_apply("f", [x], int_sort);
        let arr = m.mk_apply("a", [], array_sort);
        let stored = m.mk_store(arr, x, f_x);
        let rhs = m.mk_select(stored, x);
        let body = m.mk_eq(f_x, rhs);
        let quant = macro_from_body(&mut m, int_sort, body);

        let f = m.intern_str("f");
        let solver = MacroSolver::new();
        assert!(
            solver.contains_function(rhs, f, &m),
            "the occurs-check must see `f` under `select`/`store`"
        );

        let mut solver = MacroSolver::new();
        let found = solver
            .solve_macros(core::slice::from_ref(&quant), &mut m)
            .expect("macro solving must not error");
        assert!(
            found.is_empty(),
            "an ill-founded recursive array definition must be rejected as a macro"
        );
    }

    /// A genuinely non-recursive definition still IS a macro -- the fix must
    /// tighten the occurs-check, not disable macro extraction.
    #[test]
    fn non_recursive_definition_is_still_a_macro() {
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let array_sort = m.sorts.array(int_sort, int_sort);
        let x = m.mk_var("x", int_sort);
        let f_x = m.mk_apply("f", [x], int_sort);
        let arr = m.mk_apply("a", [], array_sort);
        let rhs = m.mk_select(arr, x);
        let body = m.mk_eq(f_x, rhs);
        let quant = macro_from_body(&mut m, int_sort, body);

        let f = m.intern_str("f");
        let mut solver = MacroSolver::new();
        let found = solver
            .solve_macros(core::slice::from_ref(&quant), &mut m)
            .expect("macro solving must not error");
        assert!(
            found.contains_key(&f),
            "`f(x) = (select a x)` is well-founded and must still be a macro"
        );
    }

    /// The occurs-check reaches every syntactic position, including the ones
    /// under quantifiers, `let` bindings, `distinct`, `xor` and bit-vector
    /// operators -- each of which the retired 17-kind edge list treated as a
    /// leaf.
    #[test]
    fn occurs_check_reaches_every_kind_of_position() {
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let bool_sort = m.sorts.bool_sort;
        let x = m.mk_var("x", int_sort);
        let f_x = m.mk_apply("f", [x], int_sort);
        let f = m.intern_str("f");
        let solver = MacroSolver::new();

        // Under a nested quantifier body.
        let y = m.mk_var("y", int_sort);
        let inner_eq = m.mk_eq(y, f_x);
        let nested = m.mk_forall([("y", int_sort)], inner_eq);
        assert!(solver.contains_function(nested, f, &m));

        // Under `distinct`.
        let zero = m.mk_int(0);
        let distinct = m.mk_distinct([f_x, zero]);
        assert!(solver.contains_function(distinct, f, &m));

        // Under `xor`.
        let p = m.mk_apply("p", [], bool_sort);
        let is_zero = m.mk_eq(f_x, zero);
        let xor = m.mk_xor(p, is_zero);
        assert!(solver.contains_function(xor, f, &m));

        // Under a quantifier *pattern* (trigger) with an `f`-free body.
        let trigger_body = m.mk_eq(y, zero);
        let with_pattern = m.mk_forall_with_patterns([("y", int_sort)], trigger_body, [vec![f_x]]);
        assert!(
            solver.contains_function(with_pattern, f, &m),
            "a trigger mentioning `f` is still an occurrence of `f`"
        );

        // A term with no `f` anywhere stays negative.
        let g_x = m.mk_apply("g", [x], int_sort);
        let clean = m.mk_distinct([g_x, zero]);
        assert!(!solver.contains_function(clean, f, &m));
    }
}
