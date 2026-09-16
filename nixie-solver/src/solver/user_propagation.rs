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
    pub(super) closed: bool,
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
}

impl Solver {
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
        Ok(())
    }

    /// Install a finite-domain CP model with all its domain/link assertions.
    /// Registration follows [`Self::register_user_propagator`]'s lifecycle.
    pub fn register_cp(
        &mut self,
        model: nixie_theories::cp::CpModel,
        tm: &mut TermManager,
    ) -> Result<(), nixie_theories::cp::CpError> {
        let (assertions, watches, propagator) = model.into_propagator();
        self.register_user_propagator(propagator, &watches, tm)?;
        for assertion in assertions {
            self.assert(assertion, tm);
        }
        Ok(())
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
                core::iter::once(&c.term)
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
        for consequence in self.state.manager.get_consequences() {
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
            return TheoryCheckResult::Conflict(clause);
        }
        let propagated = self.consequences();
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
}
