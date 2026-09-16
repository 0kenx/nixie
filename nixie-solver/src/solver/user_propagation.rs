//! Boolean user callbacks composed with the existing CDCL(T) callback.

use super::*;
use nixie_sat::{TheoryCallback, TheoryCheckResult};
use nixie_theories::user_propagator::{
    Consequence, PropagatorResult, UserPropagator, UserPropagatorManager,
};

#[derive(Default)]
pub(super) struct UserState {
    manager: UserPropagatorManager,
    literals: FxHashMap<TermId, Lit>,
    watches: Vec<(TermId, Lit)>,
    tables: Vec<nixie_theories::cp::table_proof::TableStatement>,
    domains: Vec<nixie_theories::cp::domain_proof::DomainStatement>,
    pub(super) closed: bool,
    pub(super) cp_originals: Vec<nixie_theories::cp::proof::CpStatement>,
    pub(super) unproved_callbacks: usize,
    cp_assertion_indices: FxHashSet<usize>,
    pub(super) recording: bool,
    pub(super) proof_lemmas: Vec<(TermId, Vec<TermId>)>,
    lemma_keys: FxHashSet<(TermId, Vec<TermId>)>,
    #[cfg(feature = "std")]
    pub(super) cp_proof: Option<super::CpProof>,
}
impl core::fmt::Debug for UserState {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("UserState")
            .field("propagators", &self.manager.num_propagators())
            .field("watches", &self.watches)
            .finish()
    }
}
impl UserState {
    pub(super) fn active(&self) -> bool {
        self.manager.num_propagators() != 0
    }

    fn record(&mut self, conclusion: TermId, premises: &[TermId]) {
        if !self.recording {
            return;
        }
        let key = (conclusion, premises.to_vec());
        if self.lemma_keys.insert(key.clone()) {
            self.proof_lemmas.push(key);
        }
    }

    fn certificate_valid(&self, consequence: &Consequence) -> bool {
        consequence
            .table_certificate
            .as_ref()
            .is_none_or(|certificate| {
                self.tables.iter().any(|original| {
                    certificate.is_for(original)
                        && certificate
                            .check(original, consequence.term, &consequence.justification)
                            .is_ok()
                })
            })
            && consequence
                .domain_certificate
                .as_ref()
                .is_none_or(|certificate| {
                    self.domains.iter().any(|original| {
                        certificate.is_for(original)
                            && certificate
                                .check(original, consequence.term, &consequence.justification)
                                .is_ok()
                    })
                })
    }
}

impl Solver {
    #[cfg(not(feature = "std"))]
    pub(super) fn certify_cp_result(
        &mut self,
        _: SolverResult,
        _: &mut TermManager,
    ) -> SolverResult {
        SolverResult::Unknown
    }

    /// Register a trusted Boolean user propagator before the first check and
    /// outside any assertion scope. Watches and their negations form the allowed
    /// explanation/consequence vocabulary; `false` denotes conflict.
    ///
    /// Callbacks must explain every reduction using true Boolean literals and
    /// certify complete assignments in `final_check`. The solver validates the
    /// vocabulary and current truth of reasons, but the client is responsible
    /// for their logical validity. Callbacks receive search push/pop events.
    /// Equality/disequality events and branching hints are not wired here;
    /// watch explicit Boolean equality atoms instead. See `docs/CP.md`.
    pub fn register_user_propagator(
        &mut self,
        propagator: Box<dyn UserPropagator>,
        watches: &[TermId],
        tm: &mut TermManager,
    ) -> Result<(), nixie_theories::cp::CpError> {
        use nixie_theories::cp::CpError;
        if self.user_state.closed || !self.context_stack.is_empty() {
            return Err(CpError(
                "register propagators at base scope before the first check",
            ));
        }
        if watches.iter().any(|&t| {
            !tm.get(t)
                .is_some_and(|node| node.sort == tm.sorts.bool_sort)
        }) {
            return Err(CpError("user propagator watches must be Boolean terms"));
        }
        self.invalidate_results();
        for &term in watches {
            let lit = self.encode(term, tm);
            self.sat.freeze_theory_vars([lit.var()]);
            self.user_state.literals.insert(term, lit);
            let negation = tm.mk_not(term);
            self.user_state.literals.insert(negation, !lit);
            if !self.user_state.watches.iter().any(|&(t, _)| t == term) {
                self.user_state.watches.push((term, lit));
            }
            self.user_state.manager.watch_term(term);
        }
        self.user_state.manager.register_propagator(propagator);
        self.user_state.unproved_callbacks += 1;
        Ok(())
    }

    /// Install a finite-domain CP model with all its domain/link assertions.
    /// Registration follows [`Self::register_user_propagator`]'s lifecycle.
    pub fn register_cp(
        &mut self,
        model: nixie_theories::cp::CpModel,
        tm: &mut TermManager,
    ) -> Result<(), nixie_theories::cp::CpError> {
        let original = model.statement();
        let tables = model.table_statements();
        let domains = model.domain_statements();
        let (assertions, watches, propagator) = model.into_propagator();
        self.register_user_propagator(propagator, &watches, tm)?;
        self.user_state.unproved_callbacks -= 1;
        self.user_state.cp_originals.push(original);
        self.user_state.tables.extend(tables);
        self.user_state.domains.extend(domains);
        let before = self.certificate_assertions.len();
        for assertion in assertions {
            self.assert(assertion, tm);
        }
        self.user_state
            .cp_assertion_indices
            .extend(before..self.certificate_assertions.len());
        Ok(())
    }

    // CP-generated inputs are reconstructed from declarations in a proof, not
    // imported from the main solver's assertion ledger. Registrations happen
    // at root, so these positions survive every legal assertion pop.
    pub(super) fn cp_user_assertions(&self) -> Vec<TermId> {
        self.certificate_assertions
            .iter()
            .enumerate()
            .filter(|(i, _)| !self.user_state.cp_assertion_indices.contains(i))
            .map(|(_, &term)| term)
            .collect()
    }

    pub(super) fn certification_roots(&self) -> Vec<TermId> {
        let mut roots = self.certificate_assertions.clone();
        for original in &self.user_state.cp_originals {
            roots.extend_from_slice(original.assertions());
        }
        roots
    }

    // Independent model gate, including all specialized solver early exits.
    // Never let a Sat bypass final_check, nor trust reconstructed SAT phases.
    pub(super) fn validate_user_model(&mut self, tm: &TermManager) -> bool {
        if !self.user_state.active() {
            return true;
        }
        let Some(model) = &self.model else {
            return false;
        };
        let mut values = Vec::new();
        for &(term, _) in &self.user_state.watches {
            match self.eval_in_model_outcome(term, model, tm, 0) {
                model_eval::EvalOutcome::Value(EvalVal::Bool(value)) => {
                    values.push((term, tm.mk_bool(value)))
                }
                _ => return false,
            }
        }
        self.user_state.manager.push();
        for (term, value) in values {
            self.user_state.manager.notify_fixed(term, value);
        }
        let result = self.user_state.manager.final_check();
        let consequences = self.user_state.manager.get_consequences();
        self.user_state.manager.pop(1);
        result == PropagatorResult::Sat
            && consequences.iter().all(|c| {
                self.user_state.certificate_valid(c)
                    && core::iter::once(&c.term)
                        .chain(&c.justification)
                        .all(|&term| {
                            (term == tm.mk_bool(true)
                                || term == tm.mk_bool(false)
                                || self.user_state.literals.contains_key(&term))
                                && matches!(
                                    self.eval_in_model_outcome(term, model, tm, 0),
                                    model_eval::EvalOutcome::Value(EvalVal::Bool(true))
                                )
                        })
            })
    }
}

pub(super) struct UserCallback<'a, T> {
    inner: &'a mut T,
    state: &'a mut UserState,
    true_term: TermId,
    false_term: TermId,
    level: u32,
    pub(super) invalid: bool,
}
impl<'a, T: TheoryCallback> UserCallback<'a, T> {
    pub(super) fn new(inner: &'a mut T, state: &'a mut UserState, tm: &TermManager) -> Self {
        state.manager.push();
        Self {
            inner,
            state,
            true_term: tm.mk_bool(true),
            false_term: tm.mk_bool(false),
            level: 0,
            invalid: false,
        }
    }

    fn truth(&self, literal: Lit) -> Option<bool> {
        self.state.watches.iter().find_map(|&(term, lit)| {
            if lit.var() != literal.var() {
                return None;
            }
            self.state
                .manager
                .get_fixed_value(term)
                .map(|value| (value == self.true_term) == (lit == literal))
        })
    }

    fn consequences(&mut self) -> TheoryCheckResult {
        let mut props = Vec::new();
        let consequences = self.state.manager.get_consequences();
        if consequences
            .iter()
            .any(|c| !self.state.certificate_valid(c))
        {
            self.invalid = true;
            return TheoryCheckResult::Sat;
        }
        for consequence in consequences {
            self.state
                .record(consequence.term, &consequence.justification);
            let mut reasons: SmallVec<[Lit; 8]> = SmallVec::new();
            for term in consequence.justification {
                if term == self.true_term {
                    continue;
                }
                let Some(&lit) = self.state.literals.get(&term) else {
                    self.invalid = true;
                    return TheoryCheckResult::Sat;
                };
                if self.truth(lit) != Some(true) {
                    self.invalid = true;
                    return TheoryCheckResult::Sat;
                }
                reasons.push(lit);
            }
            if consequence.term == self.true_term {
                continue;
            }
            if consequence.term == self.false_term {
                return TheoryCheckResult::Conflict(reasons.iter().map(|&l| !l).collect());
            }
            let Some(&lit) = self.state.literals.get(&consequence.term) else {
                self.invalid = true;
                return TheoryCheckResult::Sat;
            };
            match self.truth(lit) {
                Some(true) => {}
                Some(false) => {
                    let mut clause: SmallVec<[Lit; 8]> = reasons.iter().map(|&l| !l).collect();
                    clause.push(lit);
                    return TheoryCheckResult::Conflict(clause);
                }
                None => props.push((lit, reasons)),
            }
        }
        if props.is_empty() {
            TheoryCheckResult::Sat
        } else {
            TheoryCheckResult::Propagated(props)
        }
    }
}
impl<T> Drop for UserCallback<'_, T> {
    fn drop(&mut self) {
        self.state.manager.pop(self.level as usize + 1);
    }
}
impl<T: TheoryCallback> TheoryCallback for UserCallback<'_, T> {
    fn is_real_theory(&self) -> bool {
        true
    }
    fn record_lemma(&mut self, clause: &[Lit]) {
        self.inner.record_lemma(clause);
    }
    fn on_assignment(&mut self, lit: Lit) -> TheoryCheckResult {
        let result = self.inner.on_assignment(lit);
        for &(term, watched) in &self.state.watches {
            if watched.var() == lit.var() {
                let value = if watched == lit {
                    self.true_term
                } else {
                    self.false_term
                };
                if let Some(old) = self.state.manager.get_fixed_value(term) {
                    if old == value {
                        continue;
                    }
                    // A client cannot retract a fixation without a pop.
                    self.invalid = true;
                    continue;
                }
                self.state.manager.notify_fixed(term, value);
            }
        }
        if self.invalid {
            return TheoryCheckResult::Sat;
        }
        match result {
            TheoryCheckResult::Sat => self.consequences(),
            other => other,
        }
    }
    fn final_check(&mut self) -> TheoryCheckResult {
        let result = self.inner.final_check();
        if !matches!(result, TheoryCheckResult::Sat) {
            return result;
        }
        if self.invalid {
            return TheoryCheckResult::Sat;
        }
        let result = self.state.manager.final_check();
        // Validate queued table witnesses even when final_check returns a
        // conflict directly. Otherwise this early return bypasses the checker.
        let propagated = self.consequences();
        if self.invalid {
            return TheoryCheckResult::Sat;
        }
        if let PropagatorResult::Unsat(reasons) = &result {
            // Use exactly the same vocabulary/truth validation as reductions.
            let conflict = Consequence::new(self.false_term, reasons.clone());
            let mut clause = SmallVec::new();
            for term in conflict.justification {
                if term == self.true_term {
                    continue;
                }
                let Some(&lit) = self.state.literals.get(&term) else {
                    self.invalid = true;
                    return TheoryCheckResult::Sat;
                };
                if self.truth(lit) != Some(true) {
                    self.invalid = true;
                    return TheoryCheckResult::Sat;
                }
                clause.push(!lit);
            }
            self.state.record(self.false_term, reasons);
            return TheoryCheckResult::Conflict(clause);
        }
        if matches!(propagated, TheoryCheckResult::Sat) && result == PropagatorResult::Unknown {
            self.invalid = true;
        }
        propagated
    }
    fn on_new_level(&mut self, level: u32) {
        self.inner.on_new_level(level);
        while self.level < level {
            self.state.manager.push();
            self.level += 1;
        }
    }
    fn on_backtrack(&mut self, level: u32) {
        self.inner.on_backtrack(level);
        if level < self.level {
            self.state.manager.pop((self.level - level) as usize);
            self.level = level;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nixie_theories::user_propagator::PropagatorContext;

    struct FalseReason(TermId, TermId);
    impl UserPropagator for FalseReason {
        fn final_check(&mut self, ctx: &mut PropagatorContext) -> PropagatorResult {
            ctx.propagate(Consequence::new(self.0, vec![self.1]));
            PropagatorResult::Sat
        }
    }

    #[test]
    fn model_gate_checks_reasons_independently_of_search() {
        let mut tm = TermManager::new();
        let mut solver = Solver::new();
        assert!(
            solver
                .register_user_propagator(
                    Box::new(FalseReason(tm.mk_bool(true), tm.mk_bool(false))),
                    &[],
                    &mut tm
                )
                .is_ok()
        );
        solver.model = Some(Model::new());
        assert!(!solver.validate_user_model(&tm));
    }

    struct UnregisteredCertificate(Consequence);
    impl UserPropagator for UnregisteredCertificate {
        fn final_check(&mut self, ctx: &mut PropagatorContext) -> PropagatorResult {
            ctx.propagate(self.0.clone());
            PropagatorResult::Sat
        }
    }

    #[test]
    fn model_gate_checks_certificates_independently_of_search() {
        use nixie_theories::cp::{CpModel, table_proof::TableCertificate};
        let mut tm = TermManager::new();
        let mut fake = CpModel::new(&tm);
        assert!(fake.table(vec![], vec![]).is_ok());
        let Some(statement) = fake.table_statements().pop() else {
            panic!("missing original table");
        };
        let mut step = Consequence::new(tm.mk_bool(true), vec![]);
        step.table_certificate = Some(TableCertificate::new(statement, vec![]));
        let mut solver = Solver::new();
        assert!(
            solver
                .register_user_propagator(Box::new(UnregisteredCertificate(step)), &[], &mut tm)
                .is_ok()
        );
        solver.model = Some(Model::new());
        assert!(!solver.validate_user_model(&tm));
    }
    #[test]
    fn model_gate_checks_domain_certificates_independently_of_search() {
        use nixie_theories::cp::{
            CpModel,
            domain_proof::{DomainCertificate, DomainRule},
        };
        let mut tm = TermManager::new();
        let mut fake = CpModel::new(&tm);
        assert!(fake.variable(vec![], &mut tm).is_ok());
        let Some(statement) = fake.domain_statements().pop() else {
            panic!("missing original domain");
        };
        let mut step = Consequence::new(tm.mk_true(), vec![]);
        step.domain_certificate = Some(DomainCertificate::new(
            statement,
            DomainRule::Exhausted(vec![]),
        ));
        let mut solver = Solver::new();
        assert!(
            solver
                .register_user_propagator(Box::new(UnregisteredCertificate(step)), &[], &mut tm)
                .is_ok()
        );
        solver.model = Some(Model::new());
        assert!(!solver.validate_user_model(&tm));
    }
}
