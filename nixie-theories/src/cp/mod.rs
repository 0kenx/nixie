//! Explained finite-domain global constraints for the user-propagator API.
//!
//! Domains use Boolean value indicators, so no new SMT-LIB syntax or theory
//! combination axioms are needed. Values and scheduling arithmetic are exact.
//! See `docs/CP.md` for semantics, propagation strength and the trust contract.

#[allow(unused_imports)]
use crate::prelude::*;
use crate::user_propagator::{Consequence, PropagatorContext, PropagatorResult, UserPropagator};
use nixie_core::ast::{TermId, TermManager};
use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};

mod domain_explanation;
pub mod domain_proof;
mod feasibility;
pub mod proof;
mod table_explanation;
pub mod table_proof;
use table_proof::{TableData, TableStatement};

/// A finite-domain variable, local to one [`CpModel`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CpVar(usize);

/// A mandatory, non-preemptive task occupying `[start, start + duration)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Task {
    /// Finite-domain start variable.
    pub start: CpVar,
    /// Nonnegative constant duration; zero-duration tasks consume no resource.
    pub duration: BigInt,
    /// Nonnegative constant resource demand.
    pub demand: BigInt,
}

/// An optional, non-preemptive task. When `presence` is false, scheduling
/// imposes no restriction on its start and consumes no resource.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OptionalTask {
    /// Boolean condition, from the model's term manager (formulas are allowed).
    pub presence: TermId,
    /// Existing finite-domain start variable; its domain still applies if absent.
    pub start: CpVar,
    /// Nonnegative constant duration.
    pub duration: BigInt,
    /// Nonnegative constant resource demand.
    pub demand: BigInt,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Presence {
    atom: TermId,
    negation: TermId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ScheduledTask {
    task: Task,
    // Index into the model's canonical presence conditions, and required truth.
    presence: Option<(usize, bool)>,
}

/// An automaton transition `(source, symbol, destination)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Transition {
    /// Source state identifier.
    pub source: usize,
    /// Input symbol.
    pub symbol: BigInt,
    /// Destination state identifier.
    pub destination: usize,
}

/// Invalid CP construction (rejected before installing any constraint).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpError(pub &'static str);

impl core::fmt::Display for CpError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.0)
    }
}
impl core::error::Error for CpError {}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Domain {
    values: Vec<BigInt>,
    atoms: Vec<TermId>,
    negations: Vec<TermId>,
}

// One callback's immutable assignment snapshot. Witness indexes refer only
// to this snapshot's ordered reasons, never to a later callback or scope.
struct DomainSnapshot {
    values: Vec<Vec<BigInt>>,
    reasons: Vec<TermId>,
    fixed_premises: Vec<Option<usize>>,
    valid: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Constraint {
    AllDifferent(Vec<CpVar>),
    Table(TableStatement),
    Regular(Vec<CpVar>, usize, Vec<usize>, Vec<Transition>),
    Circuit(Vec<CpVar>),
    Cumulative(Vec<ScheduledTask>, BigInt),
}
impl Constraint {
    fn contains_variable(&self, var: CpVar) -> bool {
        match self {
            Self::AllDifferent(vars) | Self::Regular(vars, ..) | Self::Circuit(vars) => {
                vars.contains(&var)
            }
            Self::Table(statement) => statement.variables().contains(&var),
            Self::Cumulative(tasks, _) => tasks.iter().any(|task| task.task.start == var),
        }
    }

    fn variables(&self) -> Vec<CpVar> {
        match self {
            Self::AllDifferent(v) | Self::Regular(v, ..) | Self::Circuit(v) => v.clone(),
            Self::Table(statement) => statement.variables().to_vec(),
            Self::Cumulative(tasks, _) => tasks.iter().map(|t| t.task.start).collect(),
        }
    }
}

/// A collection of finite domains and explained global constraints.
///
/// Construct the model before registering it with `Solver::register_cp`.
/// Variable identifiers belong to this model; keep models' identifiers separate.
pub struct CpModel {
    domains: Vec<Arc<Domain>>,
    constraints: Vec<Constraint>,
    assertions: Vec<TermId>,
    bindings: Vec<(CpVar, TermId)>,
    presences: Vec<Presence>,
    true_term: TermId,
    false_term: TermId,
}

impl CpModel {
    /// Start a model using the same term manager as the SMT solver.
    pub fn new(tm: &TermManager) -> Self {
        Self {
            domains: Vec::new(),
            constraints: Vec::new(),
            assertions: Vec::new(),
            bindings: Vec::new(),
            presences: Vec::new(),
            true_term: tm.mk_bool(true),
            false_term: tm.mk_bool(false),
        }
    }

    /// Create a finite-domain variable from distinct values and fresh Boolean
    /// indicators supplied by the caller. Indicators must be Boolean variables
    /// and must not be reused by another domain in this model.
    /// An empty domain is allowed and makes the model infeasible.
    pub fn variable(
        &mut self,
        entries: Vec<(BigInt, TermId)>,
        tm: &mut TermManager,
    ) -> Result<CpVar, CpError> {
        let mut values = Vec::new();
        let mut atoms = Vec::new();
        for (value, atom) in entries {
            if !tm.get(atom).is_some_and(|t| {
                t.sort == tm.sorts.bool_sort && matches!(t.kind, nixie_core::ast::TermKind::Var(_))
            }) {
                return Err(CpError("domain indicators must be Boolean variables"));
            }
            if values.contains(&value)
                || atoms.contains(&atom)
                || self.domains.iter().any(|d| d.atoms.contains(&atom))
            {
                return Err(CpError("duplicate domain value or indicator"));
            }
            values.push(value);
            atoms.push(atom);
        }
        // The SAT core chooses at least one value. The propagator explains
        // at-most-one reductions without a quadratic eager encoding.
        self.assertions.push(tm.mk_or(atoms.iter().copied()));
        let negations = atoms.iter().map(|&a| tm.mk_not(a)).collect();
        let var = CpVar(self.domains.len());
        self.domains.push(Arc::new(Domain {
            values,
            atoms,
            negations,
        }));
        Ok(var)
    }

    /// Link a CP variable to an existing SMT Int term with exact equivalences.
    pub fn bind_integer(
        &mut self,
        var: CpVar,
        term: TermId,
        tm: &mut TermManager,
    ) -> Result<(), CpError> {
        self.validate(&[var])?;
        if !tm.get(term).is_some_and(|t| t.sort == tm.sorts.int_sort) {
            return Err(CpError("binding requires an Int term"));
        }
        self.bindings.push((var, term));
        for (value, &atom) in self.domains[var.0]
            .values
            .iter()
            .zip(&self.domains[var.0].atoms)
        {
            let constant = tm.mk_int(value.clone());
            let equality = tm.mk_eq(term, constant);
            self.assertions.push(tm.mk_eq(atom, equality));
        }
        Ok(())
    }

    fn validate(&self, vars: &[CpVar]) -> Result<(), CpError> {
        if vars.iter().any(|v| v.0 >= self.domains.len()) {
            Err(CpError("unknown CP variable"))
        } else {
            Ok(())
        }
    }

    /// Require pairwise distinct values. Repeated variables make it infeasible.
    pub fn alldifferent(&mut self, vars: Vec<CpVar>) -> Result<(), CpError> {
        self.validate(&vars)?;
        self.constraints.push(Constraint::AllDifferent(vars));
        Ok(())
    }

    /// Require membership in an allowed tuple relation (including arity zero).
    pub fn table(&mut self, vars: Vec<CpVar>, tuples: Vec<Vec<BigInt>>) -> Result<(), CpError> {
        self.validate(&vars)?;
        if tuples.iter().any(|t| t.len() != vars.len()) {
            return Err(CpError("table tuple arity mismatch"));
        }
        let domains = vars
            .iter()
            .map(|&v| (v, self.domains[v.0].clone()))
            .collect();
        self.constraints
            .push(Constraint::Table(TableStatement(Arc::new(TableData {
                variables: vars,
                rows: tuples,
                domains,
                false_term: self.false_term,
            }))));
        Ok(())
    }

    /// Retain original exactly-one domains for independent certificate checking.
    /// Statements share identity with the propagator and are never mutated.
    pub fn domain_statements(&self) -> Vec<domain_proof::DomainStatement> {
        self.domains
            .iter()
            .map(|domain| domain_proof::DomainStatement {
                domain: domain.clone(),
                false_term: self.false_term,
            })
            .collect()
    }

    /// Retain immutable original tables for independent certificate checking.
    /// Returned statements share identity with the installed propagator; later
    /// additions to the model do not alter an existing statement.
    pub fn table_statements(&self) -> Vec<TableStatement> {
        self.constraints
            .iter()
            .filter_map(|c| match c {
                Constraint::Table(statement) => Some(statement.clone()),
                Constraint::AllDifferent(_)
                | Constraint::Regular(..)
                | Constraint::Circuit(_)
                | Constraint::Cumulative(..) => None,
            })
            .collect()
    }

    /// Require an accepting automaton path. Nondeterministic transitions are
    /// supported; there are no epsilon transitions. Empty words are accepted
    /// exactly when `initial` is accepting.
    pub fn regular(
        &mut self,
        vars: Vec<CpVar>,
        initial: usize,
        accepting: Vec<usize>,
        transitions: Vec<Transition>,
    ) -> Result<(), CpError> {
        self.validate(&vars)?;
        self.constraints
            .push(Constraint::Regular(vars, initial, accepting, transitions));
        Ok(())
    }

    /// Require one Hamiltonian cycle through every node. `successors[i]` is
    /// the zero-based successor of node `i`. Self loops are valid only for a
    /// single-node circuit. The empty circuit is satisfied.
    pub fn circuit(&mut self, successors: Vec<CpVar>) -> Result<(), CpError> {
        self.validate(&successors)?;
        self.constraints.push(Constraint::Circuit(successors));
        Ok(())
    }

    /// Require resource usage at every time to be at most `capacity`.
    /// Durations and demands must be nonnegative; negative capacity is an
    /// infeasible constraint, even for an empty task list.
    pub fn cumulative(&mut self, tasks: Vec<Task>, capacity: BigInt) -> Result<(), CpError> {
        self.validate(&tasks.iter().map(|t| t.start).collect::<Vec<_>>())?;
        if tasks
            .iter()
            .any(|t| t.duration < BigInt::zero() || t.demand < BigInt::zero())
        {
            return Err(CpError("negative duration or demand"));
        }
        self.constraints.push(Constraint::Cumulative(
            tasks
                .into_iter()
                .map(|task| ScheduledTask {
                    task,
                    presence: None,
                })
                .collect(),
            capacity,
        ));
        Ok(())
    }

    /// Require cumulative capacity for the tasks whose Boolean conditions hold.
    /// Constants and arbitrary Boolean formulas are accepted; use `true` to mix
    /// mandatory tasks into the same resource. Construction is atomic on error.
    pub fn cumulative_optional(
        &mut self,
        tasks: Vec<OptionalTask>,
        capacity: BigInt,
        tm: &mut TermManager,
    ) -> Result<(), CpError> {
        self.validate(&tasks.iter().map(|t| t.start).collect::<Vec<_>>())?;
        for task in &tasks {
            if task.duration < BigInt::zero() || task.demand < BigInt::zero() {
                return Err(CpError("negative duration or demand"));
            }
            if !tm
                .get(task.presence)
                .is_some_and(|t| t.sort == tm.sorts.bool_sort)
            {
                return Err(CpError("task presence must be a Boolean term"));
            }
        }
        let mut scheduled = Vec::new();
        for task in tasks {
            let (atom, positive) = match tm.get(task.presence).map(|t| &t.kind) {
                Some(nixie_core::ast::TermKind::Not(inner)) => (*inner, false),
                Some(_) => (task.presence, true),
                None => return Err(CpError("missing task presence term")),
            };
            let index = match self.presences.iter().position(|p| p.atom == atom) {
                Some(index) => index,
                None => {
                    let index = self.presences.len();
                    self.presences.push(Presence {
                        atom,
                        negation: tm.mk_not(atom),
                    });
                    index
                }
            };
            scheduled.push(ScheduledTask {
                task: Task {
                    start: task.start,
                    duration: task.duration,
                    demand: task.demand,
                },
                presence: Some((index, positive)),
            });
        }
        self.constraints
            .push(Constraint::Cumulative(scheduled, capacity));
        Ok(())
    }

    /// Retain immutable original declarations for complete proof checking.
    pub fn statement(&self) -> proof::CpStatement {
        proof::CpStatement {
            domains: self.domains.clone(),
            constraints: self.constraints.clone(),
            assertions: self.assertions.clone(),
            bindings: self.bindings.clone(),
            presences: self.presences.clone(),
            true_term: self.true_term,
            false_term: self.false_term,
        }
    }

    /// Consume the model into domain assertions, watched Boolean atoms, and
    /// a callback. All assertions must be installed together with the callback.
    pub fn into_propagator(mut self) -> (Vec<TermId>, Vec<TermId>, Box<dyn UserPropagator>) {
        let assertions = core::mem::take(&mut self.assertions);
        let watches = self
            .domains
            .iter()
            .flat_map(|d| d.atoms.iter().copied())
            .chain(self.presences.iter().map(|p| p.atom))
            .collect();
        (assertions, watches, Box::new(self))
    }

    fn domains(&self, ctx: &PropagatorContext) -> DomainSnapshot {
        let mut reasons = Vec::new();
        let mut fixed_premises = Vec::with_capacity(self.domains.len());
        let mut valid = true;
        let domains = self
            .domains
            .iter()
            .map(|d| {
                let mut fixed = None;
                let mut fixed_premise = None;
                let mut remaining = Vec::new();
                for (i, &atom) in d.atoms.iter().enumerate() {
                    match ctx.get_fixed_value(atom) {
                        Some(v) if v == self.true_term => {
                            fixed_premise = Some(reasons.len());
                            reasons.push(atom);
                            if fixed.is_some() {
                                valid = false;
                            }
                            fixed = Some(d.values[i].clone());
                            remaining.push(d.values[i].clone());
                        }
                        Some(v) if v == self.false_term => reasons.push(d.negations[i]),
                        Some(_) => {
                            valid = false;
                        }
                        None => remaining.push(d.values[i].clone()),
                    }
                }
                fixed_premises.push(fixed_premise);
                if let Some(value) = fixed {
                    vec![value]
                } else {
                    remaining
                }
            })
            .collect();
        DomainSnapshot {
            values: domains,
            reasons,
            fixed_premises,
            valid,
        }
    }

    fn run(&self, ctx: &mut PropagatorContext) -> PropagatorResult {
        let DomainSnapshot {
            values: domains,
            mut reasons,
            fixed_premises,
            valid,
        } = self.domains(ctx);
        let mut presences = Vec::new();
        for presence in &self.presences {
            let fixed = if presence.atom == self.true_term {
                Some(self.true_term)
            } else if presence.atom == self.false_term {
                Some(self.false_term)
            } else {
                ctx.get_fixed_value(presence.atom)
            };
            let value = match fixed {
                Some(v) if v == self.true_term => {
                    reasons.push(presence.atom);
                    Some(true)
                }
                Some(v) if v == self.false_term => {
                    reasons.push(presence.negation);
                    Some(false)
                }
                Some(_) => return PropagatorResult::Unknown,
                None => None,
            };
            presences.push(value);
        }
        if !valid {
            // Unknown fixed values cannot justify a conflict. Boolean-only
            // registration guarantees the normal path uses true/false terms.
            if self.domains.iter().flat_map(|d| &d.atoms).any(|&a| {
                ctx.get_fixed_value(a)
                    .is_some_and(|v| v != self.true_term && v != self.false_term)
            }) {
                return PropagatorResult::Unknown;
            }
            let Some(consequence) = self.explain(None, self.false_term, &reasons) else {
                return PropagatorResult::Unknown;
            };
            ctx.propagate(consequence);
            return PropagatorResult::Unsat(reasons);
        }
        if domains.iter().any(Vec::is_empty) {
            let Some(consequence) = self.explain(None, self.false_term, &reasons) else {
                return PropagatorResult::Unknown;
            };
            ctx.propagate(consequence);
            return PropagatorResult::Unsat(reasons);
        }
        let feasibility = feasibility::Feasibility::new(&domains);
        for constraint in &self.constraints {
            match feasibility.feasible(constraint, &presences) {
                Some(true) => {}
                Some(false) => {
                    let Some(consequence) =
                        self.explain(Some(constraint), self.false_term, &reasons)
                    else {
                        return PropagatorResult::Unknown;
                    };
                    ctx.propagate(consequence);
                    return PropagatorResult::Unsat(reasons);
                }
                None => return PropagatorResult::Unknown,
            }
        }
        // Each exclusion is proved independently against the callback's
        // current domains. No unexplained local reduction feeds another one.
        for (i, d) in self.domains.iter().enumerate() {
            for (j, &atom) in d.atoms.iter().enumerate() {
                if ctx.get_fixed_value(atom).is_some() {
                    continue;
                }
                let mut excluded = !domains[i].contains(&d.values[j]);
                let mut witness_constraint = None;
                let mut materialized = None;
                for constraint in self
                    .constraints
                    .iter()
                    .filter(|c| c.contains_variable(CpVar(i)))
                {
                    let feasible = match constraint {
                        Constraint::Cumulative(..) => {
                            feasibility.feasible_at(constraint, &presences, CpVar(i), &d.values[j])
                        }
                        Constraint::AllDifferent(_)
                        | Constraint::Table(_)
                        | Constraint::Regular(..)
                        | Constraint::Circuit(_) => {
                            // Preserve one copy per value (not per global) for
                            // non-scheduling constraints sharing this variable.
                            let candidate = materialized.get_or_insert_with(|| {
                                let mut candidate = domains.clone();
                                candidate[i] = vec![d.values[j].clone()];
                                candidate
                            });
                            feasibility::Feasibility::new(candidate)
                                .feasible(constraint, &presences)
                        }
                    };
                    match feasible {
                        Some(true) => {}
                        Some(false) => {
                            excluded = true;
                            witness_constraint = Some(constraint);
                            break;
                        }
                        None => return PropagatorResult::Unknown,
                    }
                }
                if excluded {
                    let consequence = if let Some(constraint) = witness_constraint {
                        self.explain(Some(constraint), d.negations[j], &reasons)
                    } else {
                        // In a valid snapshot an unknown indicator can leave
                        // its domain only because another indicator is true.
                        // Indicators are unique across domains. Use the known
                        // domain and premise instead of searching them again;
                        // the independent rule checker still checks every hint.
                        fixed_premises[i].and_then(|fixed| {
                            let statement = domain_proof::DomainStatement {
                                domain: d.clone(),
                                false_term: self.false_term,
                            };
                            let certificate =
                                statement.explain_fixed(d.negations[j], &reasons, fixed)?;
                            let mut consequence = Consequence::new(d.negations[j], reasons.clone());
                            consequence.domain_certificate = Some(certificate);
                            Some(consequence)
                        })
                    };
                    let Some(consequence) = consequence else {
                        return PropagatorResult::Unknown;
                    };
                    ctx.propagate(consequence);
                }
            }
        }
        // Test each unknown condition in both polarities. All tasks sharing
        // it change together. Only the original callback state is a premise;
        // the trial assignment is discharged into the opposite conclusion.
        for (index, presence) in self.presences.iter().enumerate() {
            if presences[index].is_some() {
                continue;
            }
            for truth in [false, true] {
                let mut candidate = presences.clone();
                candidate[index] = Some(truth);
                for constraint in &self.constraints {
                    match feasibility.presence_feasible(constraint, &candidate) {
                        Some(true) => {}
                        Some(false) => {
                            let conclusion = if truth {
                                presence.negation
                            } else {
                                presence.atom
                            };
                            let Some(consequence) =
                                self.explain(Some(constraint), conclusion, &reasons)
                            else {
                                return PropagatorResult::Unknown;
                            };
                            ctx.propagate(consequence);
                            break;
                        }
                        None => return PropagatorResult::Unknown,
                    }
                }
            }
        }
        if domains.iter().all(|d| d.len() == 1) && presences.iter().all(Option::is_some) {
            PropagatorResult::Sat
        } else {
            PropagatorResult::Unknown
        }
    }

    fn explain(
        &self,
        constraint: Option<&Constraint>,
        term: TermId,
        reasons: &[TermId],
    ) -> Option<Consequence> {
        let mut consequence = Consequence::new(term, reasons.to_vec());
        match constraint {
            Some(Constraint::Table(statement)) => {
                consequence.table_certificate = Some(statement.explain(term, reasons)?);
            }
            None => {
                consequence.domain_certificate = Some(self.domains.iter().find_map(|domain| {
                    domain_proof::DomainStatement {
                        domain: domain.clone(),
                        false_term: self.false_term,
                    }
                    .explain(term, reasons)
                })?);
            }
            Some(
                Constraint::AllDifferent(_)
                | Constraint::Regular(..)
                | Constraint::Circuit(_)
                | Constraint::Cumulative(..),
            ) => {}
        }
        Some(consequence)
    }
}

impl UserPropagator for CpModel {
    fn on_fixed(&mut self, _term: TermId, _value: TermId, ctx: &mut PropagatorContext) {
        self.run(ctx);
    }
    fn final_check(&mut self, ctx: &mut PropagatorContext) -> PropagatorResult {
        self.run(ctx)
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod optional_tests;
