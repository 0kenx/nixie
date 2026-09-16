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

mod feasibility;
mod table_explanation;
pub mod table_proof;
use table_proof::{TableData, TableStatement};

/// A finite-domain variable, local to one [`CpModel`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CpVar(usize);

/// A mandatory, non-preemptive task occupying `[start, start + duration)`.
#[derive(Debug, Clone)]
pub struct Task {
    /// Finite-domain start variable.
    pub start: CpVar,
    /// Nonnegative constant duration; zero-duration tasks consume no resource.
    pub duration: BigInt,
    /// Nonnegative constant resource demand.
    pub demand: BigInt,
}

/// An automaton transition `(source, symbol, destination)`.
#[derive(Debug, Clone)]
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

#[derive(Clone)]
enum Constraint {
    AllDifferent(Vec<CpVar>),
    Table(TableStatement),
    Regular(Vec<CpVar>, usize, Vec<usize>, Vec<Transition>),
    Circuit(Vec<CpVar>),
    Cumulative(Vec<Task>, BigInt),
}
impl Constraint {
    fn variables(&self) -> Vec<CpVar> {
        match self {
            Self::AllDifferent(v) | Self::Regular(v, ..) | Self::Circuit(v) => v.clone(),
            Self::Table(statement) => statement.variables().to_vec(),
            Self::Cumulative(tasks, _) => tasks.iter().map(|t| t.start).collect(),
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
        self.constraints
            .push(Constraint::Cumulative(tasks, capacity));
        Ok(())
    }

    /// Consume the model into domain assertions, watched Boolean atoms, and
    /// a callback. All assertions must be installed together with the callback.
    pub fn into_propagator(mut self) -> (Vec<TermId>, Vec<TermId>, Box<dyn UserPropagator>) {
        let assertions = core::mem::take(&mut self.assertions);
        let watches = self
            .domains
            .iter()
            .flat_map(|d| d.atoms.iter().copied())
            .collect();
        (assertions, watches, Box::new(self))
    }

    fn domains(&self, ctx: &PropagatorContext) -> (Vec<Vec<BigInt>>, Vec<TermId>, bool) {
        let mut reasons = Vec::new();
        let mut valid = true;
        let domains = self
            .domains
            .iter()
            .map(|d| {
                let mut fixed = None;
                let mut remaining = Vec::new();
                for (i, &atom) in d.atoms.iter().enumerate() {
                    match ctx.get_fixed_value(atom) {
                        Some(v) if v == self.true_term => {
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
                if let Some(value) = fixed {
                    vec![value]
                } else {
                    remaining
                }
            })
            .collect();
        (domains, reasons, valid)
    }

    fn run(&self, ctx: &mut PropagatorContext) -> PropagatorResult {
        let (domains, reasons, valid) = self.domains(ctx);
        if !valid {
            // Unknown fixed values cannot justify a conflict. Boolean-only
            // registration guarantees the normal path uses true/false terms.
            if self.domains.iter().flat_map(|d| &d.atoms).any(|&a| {
                ctx.get_fixed_value(a)
                    .is_some_and(|v| v != self.true_term && v != self.false_term)
            }) {
                return PropagatorResult::Unknown;
            }
            ctx.propagate(Consequence::new(self.false_term, reasons.clone()));
            return PropagatorResult::Unsat(reasons);
        }
        if domains.iter().any(Vec::is_empty) {
            ctx.propagate(Consequence::new(self.false_term, reasons.clone()));
            return PropagatorResult::Unsat(reasons);
        }
        for constraint in &self.constraints {
            match self.feasible(constraint, &domains) {
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
                let mut candidate = domains.clone();
                candidate[i] = vec![d.values[j].clone()];
                let mut excluded = !domains[i].contains(&d.values[j]);
                let mut witness_constraint = None;
                for constraint in self
                    .constraints
                    .iter()
                    .filter(|c| c.variables().contains(&CpVar(i)))
                {
                    match self.feasible(constraint, &candidate) {
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
                    let Some(consequence) =
                        self.explain(witness_constraint, d.negations[j], &reasons)
                    else {
                        return PropagatorResult::Unknown;
                    };
                    ctx.propagate(consequence);
                }
            }
        }
        if domains.iter().all(|d| d.len() == 1) {
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
        if let Some(Constraint::Table(statement)) = constraint {
            consequence.table_certificate = Some(statement.explain(term, reasons)?);
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
