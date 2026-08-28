//! NIA-over-LP relaxation dispatch (upstream v0.3.3's `arithmetic::nla`
//! wiring), deliberately OUTSIDE the `nlsat` feature gate: the engine is
//! `std`-gated upstream too, so both feature builds carry it.

use super::Solver;
use crate::solver::types::{Model, SolverResult};
use oxiz_core::ast::{TermId, TermKind, TermManager};

impl Solver {
    /// Run the NIA-over-LP relaxation engine over the assertions.
    ///
    /// Slotted *after* the cell-decomposition dispatch (so no CAD verdict can
    /// move — the wiring is a completeness gain, not a parity risk) and
    /// *before* the two sat-only model searches (it can derive `unsat`;
    /// they cannot). `Unsat` is proof-backed: `nla` produces it only from an
    /// LP infeasibility closure over consequences over `Z` of the input, with
    /// exhaustive case splits (see that module's soundness contract); a
    /// dropped conjunct only weakens, so an infeasible relaxation still
    /// refutes the original. `Sat` is advisory by that same contract, so it
    /// is not taken on trust: the witness is re-checked with `holds_under`
    /// against the untouched assertions in exact `BigRational` arithmetic and
    /// a model is installed only if it really satisfies them. A witness that
    /// fails yields no verdict and the caller falls through. (Ported from
    /// upstream v0.3.3.)
    pub(super) fn dispatch_nla_relaxation(
        &mut self,
        manager: &mut TermManager,
    ) -> Option<SolverResult> {
        use oxiz_theories::arithmetic::nla::{self, NlaConfig, NlaVerdict};
        use oxiz_theories::nl_eval::holds_under;

        if !self.config.nonlinear_relaxation_engine {
            return None;
        }
        match nla::check_assertions(&self.assertions, manager, &NlaConfig::default()) {
            NlaVerdict::Unsat => Some(SolverResult::Unsat),
            NlaVerdict::Sat(witness) => {
                // Re-verify before installing: `Sat` is advisory upstream of
                // here, and this crate's own gate is the stricter one.
                if !holds_under(&self.assertions, manager, &witness) {
                    return None;
                }
                self.adopt_interpretation(witness, manager)
                    .then_some(SolverResult::Sat)
            }
            NlaVerdict::Unknown => None,
        }
    }

    /// Install an exact `Interpretation` witness as this solver's model.
    ///
    /// Returns `false` (installing nothing) when a value cannot be
    /// represented in the term language — an Int-sorted term with a
    /// fractional witness, or a real with no exact `Rational64` narrowing —
    /// which leaves the verdict to the caller rather than publishing a model
    /// that was not re-checked.
    fn adopt_interpretation(
        &mut self,
        witness: oxiz_theories::nl_eval::Interpretation,
        manager: &mut TermManager,
    ) -> bool {
        use num_traits::ToPrimitive;
        let int_sort = manager.sorts.int_sort;
        let mut model = Model::new();
        for (term, value) in witness.numeric_entries() {
            let is_integer_sorted = manager.get(term).is_some_and(|t| t.sort == int_sort);
            let value_term = if is_integer_sorted {
                if !value.is_integer() {
                    return false;
                }
                manager.mk_int(value.to_integer())
            } else {
                let Some(numer) = value.numer().to_i64() else {
                    return false;
                };
                let Some(denom) = value.denom().to_i64() else {
                    return false;
                };
                manager.mk_real(num_rational::Rational64::new(numer, denom))
            };
            model.set(term, value_term);
        }
        for (term, value) in witness.truth_entries() {
            let value_term = if value {
                manager.mk_true()
            } else {
                manager.mk_false()
            };
            model.set(term, value_term);
        }
        self.model = Some(model);
        true
    }
}

/// Whether `term` contains a nonlinear product (public re-export of the
/// gated module's classifier for the ungated dispatch site).
pub(super) fn term_is_nonlinear_pub(term: TermId, manager: &TermManager) -> bool {
    term_is_nonlinear(term, manager)
}

/// Whether every arithmetic leaf in `term` is Int-sorted (the relaxation
/// engine's precondition: its case splits are tautologies over `Z`, not `R`).
pub(super) fn term_is_integer_sorted_pub(term: TermId, manager: &TermManager) -> bool {
    /// Iterative walk: term depth is input-controlled.
    fn all_int(term: TermId, manager: &TermManager) -> bool {
        let mut stack = vec![term];
        let mut seen = rustc_hash::FxHashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            let Some(td) = manager.get(t) else { continue };
            match &td.kind {
                TermKind::IntConst(_) => {}
                TermKind::RealConst(_) => return false,
                TermKind::Var(_) => {
                    if td.sort != manager.sorts.int_sort && td.sort != manager.sorts.bool_sort {
                        return false;
                    }
                }
                TermKind::Add(_)
                | TermKind::Sub(_, _)
                | TermKind::Mul(_)
                | TermKind::Div(_, _)
                | TermKind::Mod(_, _)
                | TermKind::Neg(_) => {
                    if td.sort == manager.sorts.real_sort {
                        return false;
                    }
                    stack.extend(oxiz_core::ast::traversal::get_children(&td.kind));
                }
                _ => {
                    // Booleans and everything else: descend for numeric leaves.
                    stack.extend(oxiz_core::ast::traversal::get_children(&td.kind));
                }
            }
        }
        true
    }
    all_int(term, manager)
}

/// Local re-implementation of the nonlinear-product classifier (the gated
/// module owns the original; this copy keeps the ungated dispatch site free
/// of the feature).
fn term_is_nonlinear(term: TermId, manager: &TermManager) -> bool {
    let mut stack = vec![term];
    let mut seen = rustc_hash::FxHashSet::default();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        let Some(td) = manager.get(t) else { continue };
        if let TermKind::Mul(args) = &td.kind {
            let nonconst = args
                .iter()
                .filter(|a| {
                    !matches!(
                        manager.get(**a).map(|d| &d.kind),
                        Some(TermKind::IntConst(_)) | Some(TermKind::RealConst(_))
                    )
                })
                .count();
            if nonconst >= 2 {
                return true;
            }
        }
        stack.extend(oxiz_core::ast::traversal::get_children(&td.kind));
    }
    false
}
